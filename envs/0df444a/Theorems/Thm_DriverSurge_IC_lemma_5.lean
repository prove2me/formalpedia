-- Prove2me | Theorems.Thm_DriverSurge_IC_lemma_5
-- name    : DriverSurge.IC.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:31:36.202552+00:00
-- url     : https://prove2.me/theorems/081ac5da-cc85-44b0-974f-4e7d4ef8ac42
-- title:
--   Lemma 5, pp. 50–51 — if r(u, σ) (same sign as ∂/∂u R̂) is positive / increasing / decreasing / quasi-convex / quasi-concave near the optimum, a policy of the matching interval form is better
-- statement:
--   Let $F$ be a probability measure on $(0,\infty)$ with a bounded density $f$, and let $\hat R$ be a function of open sets $\sigma\subseteq(0,\infty)$ with values in $[0,\infty)$. Assume:
--
--   1. $\hat R$ is continuous in $\sigma$ (with respect to $F(\sigma\triangle\sigma')$), and the marginal gain $D(\sigma,u)=\partial\hat R(\sigma)/\partial u$ exists for every open $\sigma$ and every $u>0$;
--   2. $D(\sigma,u)$ is continuous in $u$ for each fixed $\sigma$;
--   3. $D(\sigma,u)$ is continuous in $\sigma$ for each fixed $u$;
--
--   and let $r(u,\sigma)$ have the same sign as $D(\sigma,u)$ whenever $f(u)>0$. Let $\sigma'\subseteq(0,\infty)$ be open with $F(\sigma')>0$ and $\hat R(\sigma')>\hat R(\emptyset)$. Then for each row of the table
--
--   | Property of $u\mapsto r(u,\sigma)$ on $(0,\infty)$ | Form of $\sigma^*$ |
--   |---|---|
--   | positive | $(0,\infty)$ |
--   | strictly increasing | $(\ell^*,\infty)$, $\ell^*\in[0,\infty)$ |
--   | strictly decreasing | $(0,u^*)$, $u^*\in[0,\infty]$ |
--   | strictly quasi-convex | $(0,\ell^*)\cup(u^*,\infty)$, $\ell^*,u^*\in[0,\infty]$ |
--   | strictly quasi-concave | $(\ell^*,u^*)$, $\ell^*,u^*\in[0,\infty]$ |
--
--   the following holds: if for some $\varepsilon>0$ the property holds for every open $\sigma$ with $\hat R(\sigma)\ge\hat R(\sigma')-\varepsilon$, then there is $\sigma^*$ of the row's form with
--   $$\hat R(\sigma^*)\ge\hat R(\sigma'),$$
--   and the inequality is strict unless $\sigma'$ is itself of that form up to an $F$-null set.
--
--   This is the structural engine of the paper: it turns sign information on the endpoint derivative into the shape of an optimal acceptance set, without restricting the competing policies to intervals.
--
--   **Formalization Note** $\hat R$ is a function on all subsets of $\mathbb R$ whose hypotheses are imposed on open subsets of $(0,\infty)$; strict quasi-convexity is the derivative-based definition of p. 63.
--
--   Differences from the source:
--   - reading: "$\hat R(\sigma)$ is continuous in $\sigma$", "continuous in $\sigma$" → continuity with respect to the pseudometric $F(\sigma\triangle\sigma')$; reason: the metric used in the proof (p. 52)
--   - reading: "the partial derivative of $\hat R$ with respect to an upper end-point $u$ … the infinitesimal gain … by adding $u$ to the set $\sigma$" → the marginal gain $\lim_{h\downarrow0}(\hat R(\sigma\cup(u,u+h))-\hat R(\sigma\setminus[u,u+h]))/h$ at every $u>0$; reason: the paper's own description (p. 50)
--   - reading: "$R(\sigma^*)\ge R(\sigma')$" → $\hat R(\sigma^*)\ge\hat R(\sigma')$; reason: typo: the lemma is about $\hat R$
--   - reading: "unless $\sigma'$ is also of the same form" → unless $\sigma'$ equals a set of that form up to an $F$-null set; reason: §2.2 (p. 6): "when we write equalities with policies σ, we mean equality up to changes of measure 0"
--   - reading: "strictly quasi-convex in $u$" → the definition of p. 63: the derivative in $u$ is strictly negative on $(0,U)$ and strictly positive on $(U,\infty)$ for some $U\in[0,\infty]$; reason: the paper's own definition (proof of Lemma 7, p. 63), with the turning point allowed at $0$ or $\infty$
-- source:
--   Garg, Nazerzadeh, Driver Surge Pricing, arXiv:1905.07544v4, pp. 50–51, Lemma 5 (proof pp. 51–55)

import Mathlib
import Definitions.Def_DriverSurge_IC_Pricing

namespace DriverSurge.IC

open MeasureTheory Set

/-- Lemma 5 (pp. 50–51). Let `F` be a probability measure on `(0, ∞)` with a bounded density `f`, and
let `R̂` be a set function, nonnegative on open subsets of `(0, ∞)`, such that
1. `R̂` is continuous in `σ` (pseudometric `F(σ △ σ')`) and the marginal gain `∂/∂u R̂(σ) = D(σ, u)`
   exists for all open `σ ⊆ (0, ∞)` and `u > 0`;
2. `D(σ, ·)` is continuous on `(0, ∞)` for each fixed `σ`;
3. `D(·, u)` is continuous in `σ` for each fixed `u > 0`;
and let `r(u, σ)` have the sign of `D(σ, u)` wherever `f(u) > 0`. Let `σ'` be open in `(0, ∞)` with
`F(σ') > 0` and `R̂(σ') > R̂(∅)`. Then, for each row of the table: if for some `ε > 0`, `r(·, σ)` has the
row's property on `(0, ∞)` for every open `σ` with `R̂(σ) ≥ R̂(σ') − ε`, then some `σ*` of the row's form
has `R̂(σ*) ≥ R̂(σ')`, strictly unless `σ'` is itself of that form up to an `F`-null set.
Rows: positive → `(0, ∞)`; strictly increasing → `(ℓ*, ∞)`, `ℓ* ∈ [0, ∞)`; strictly decreasing →
`(0, u*)`, `u* ∈ [0, ∞]`; strictly quasi-convex → `(0, ℓ*) ∪ (u*, ∞)`; strictly quasi-concave →
`(ℓ*, u*)`, `ℓ*, u* ∈ [0, ∞]`. -/
theorem lemma_5 (F : Measure ℝ) [IsProbabilityMeasure F] (hF0 : F (Iic 0) = 0) (f : ℝ → ℝ)
    (hfm : Measurable f) (hfb : ∃ B : ℝ, ∀ x, 0 ≤ f x ∧ f x ≤ B)
    (hfF : F = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (R : Set ℝ → ℝ) (hR0 : ∀ s, IsAdmissible s → 0 ≤ R s) (D : Set ℝ → ℝ → ℝ)
    (h1 : ContinuousInSet F R)
    (h1' : ∀ s, IsAdmissible s → ∀ u : ℝ, 0 < u → HasMarginalGain R s u (D s u))
    (h2 : ∀ s, IsAdmissible s → ContinuousOn (D s) (Ioi 0))
    (h3 : ∀ u : ℝ, 0 < u → ContinuousInSet F (fun s => D s u))
    (r : ℝ → Set ℝ → ℝ)
    (hr : ∀ s, IsAdmissible s → ∀ u : ℝ, 0 < u → 0 < f u →
      SignType.sign (r u s) = SignType.sign (D s u))
    (σ' : Set ℝ) (hσ' : IsAdmissible σ') (hFσ' : 0 < F σ') (hRσ' : R ∅ < R σ') :
    ((∃ ε > 0, ∀ s, IsAdmissible s → R σ' - ε ≤ R s → ∀ u : ℝ, 0 < u → 0 < r u s) →
      R σ' ≤ R (Ioi 0) ∧ (¬ EqUpToNull F σ' (Ioi 0) → R σ' < R (Ioi 0))) ∧
    ((∃ ε > 0, ∀ s, IsAdmissible s → R σ' - ε ≤ R s → StrictMonoOn (fun u => r u s) (Ioi 0)) →
      ∃ σs, IsUpperForm σs ∧ R σ' ≤ R σs ∧
        ((¬ ∃ t, IsUpperForm t ∧ EqUpToNull F σ' t) → R σ' < R σs)) ∧
    ((∃ ε > 0, ∀ s, IsAdmissible s → R σ' - ε ≤ R s → StrictAntiOn (fun u => r u s) (Ioi 0)) →
      ∃ σs, IsLowerForm σs ∧ R σ' ≤ R σs ∧
        ((¬ ∃ t, IsLowerForm t ∧ EqUpToNull F σ' t) → R σ' < R σs)) ∧
    ((∃ ε > 0, ∀ s, IsAdmissible s → R σ' - ε ≤ R s → StrictQuasiconvexIoi (fun u => r u s)) →
      ∃ σs, IsTwoSidedForm σs ∧ R σ' ≤ R σs ∧
        ((¬ ∃ t, IsTwoSidedForm t ∧ EqUpToNull F σ' t) → R σ' < R σs)) ∧
    ((∃ ε > 0, ∀ s, IsAdmissible s → R σ' - ε ≤ R s → StrictQuasiconcaveIoi (fun u => r u s)) →
      ∃ σs, IsBandForm σs ∧ R σ' ≤ R σs ∧
        ((¬ ∃ t, IsBandForm t ∧ EqUpToNull F σ' t) → R σ' < R σs)) := by sorry

end DriverSurge.IC
