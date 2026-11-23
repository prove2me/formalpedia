-- Prove2me | Theorems.Thm_ArapostathisAC_VanishingDiscount_Supplement_theorem_5_12
-- name    : ArapostathisAC.VanishingDiscount.Supplement.theorem_5_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:13:36.516904+00:00
-- url     : https://prove2.me/theorems/4ddeaf0e-3437-4bf3-b8d9-3c3a00b239fd
-- title:
--   Theorem 5.12 (corrected: the overloaded $w$ and $h$ in the last class are read as candidate $u$ and Lyapunov function $W$) — uniqueness of the ACOE solution $(\rho^*,h)$ of (5.20)
-- statement:
--   Under the standing assumptions of §5.3, let $\rho^*=\inf_{f\in\Pi_{SSR}}\int c\,d\hat\eta(f)$, let $f_0\in\Pi_{SD}$ be sample path average cost optimal, and let
--   $$h(i)=E^{f_0}_i\Big[\sum_{t=0}^{\tau-1}\big(c(X_t,f_0(X_t))-\rho^*\big)\Big],\qquad\tau=\min\{t\ge1:X_t=0\},\tag{5.20}$$
--   where $E^{f_0}_i[\tau]$ and $E^{f_0}_i[\sum_{t<\tau}c]$ are finite.
--
--   1. Assume Assumption 5.18 and stability under local perturbations (Assumption 5.21). Let $H=\{(\rho,w):(\rho,w)\text{ solves the ACOE},\ w(0)=0,\ \inf w>-\infty\}$. Then $(\rho^*,h)\in H$, and every $(\rho',w')\in H$ has $\rho'\ge\rho^*$, with equality if and only if $w'=h$.
--   2. Assume instead that $c$ is bounded and the Lyapunov condition holds for $W:S\to\mathbb R_+$, a finite $B\ni0$ and $\varepsilon>0$: (a) $\{i\notin B:P(j\mid i,a)>0\text{ for some }j\in B,a\in A\}$ is finite; (b) $W(i)\to\infty$; (c) $E^\pi_\mu[(W(X_{t+1})-W(X_t)+\varepsilon)I\{X_t\notin B\}\mid\mathfrak F_t]\le0$; (d) $\mathcal P^\pi_\mu(|W(X_{t+1})-W(X_t)|>b\mid\mathfrak F_t)\le P(Z>b)$ for $b\ge0$, with $E[e^{\lambda Z}]<\infty$ for some $\lambda>0$. Then $(\rho^*,h)$ solves the ACOE, $h(0)=0$, $\limsup_{i\to\infty}h(i)/W(i)<\infty$, and it is the unique solution of the ACOE in the class
--   $$\Big\{(\rho,u):u(0)=0,\ \limsup_{i\to\infty}u(i)/W(i)<\infty\Big\}.$$
--
--   The theorem characterizes the solution of the ACOE produced by the convex analytic approach, in the near-monotone case by minimality of $\rho$ and in the stable case by a growth class.
--
--   **Formalization Note** (c) and (d) are stated in their equivalent one-step forms ($\sum_jP(j\mid i,a)W(j)+\varepsilon\le W(i)$ for $i\notin B$; $P(\{j:|W(j)-W(i)|>b\}\mid i,a)\le\zeta((b,\infty))$ with $\zeta$ the law of $Z$). $\limsup u(i)/W(i)<\infty$ is the statement that $u/W$ is eventually bounded above. The ACOE requires summable series and an attained minimum.
--
--   Differences from the source:
--   - reading: the standing assumptions of §5.3 (p. 309): U(i) replicas of one compact metric A, S the single communicating class under every f ∈ Π_SR → CMP with U(i) = A, A compact metric (with its automatic second countability as an instance), irreducibility under every stationary randomized policy; reason: these are the section's stated standing assumptions
--   - correction: the last display prints the class {(ρ, w) : w(0) = 0, limsup_{i→∞} h(i)/w(i) < ∞}, with w also the Lyapunov function and h the fixed function (5.20) → the class {(ρ, u) : u(0) = 0, limsup_{i→∞} u(i)/W(i) < ∞}, W the Lyapunov function of (a)–(d); reason: with the printed letters the growth condition constrains only the fixed h, so the class is every pair with w(0) = 0 and uniqueness would be claimed among all ACOE solutions, which the near-monotone part shows is not the intended content; the candidate must be compared with the Lyapunov function
--   - reading: the preceding paragraph: (h, ρ*) satisfies the ACOE under Assumption 5.21 → Assumption 5.21 is a hypothesis of the first part; reason: Theorem 5.12 refers to f₀, h 'defined as above', where the ACOE property of (5.20) is stated under Assumption 5.21; in the second part it follows from (c) and bounded c
--   - reading: (5.20) is an expectation of a signed sum → E^{f₀}_i[τ] < ∞ and E^{f₀}_i[∑_{t<τ} c] < ∞ for every i are hypotheses, and h(i) = E[∑_{t<τ} c] − ρ* E[τ]; reason: the paper treats h(i) as a finite number; these are the conditions under which the expectation exists
--   - reading: ρ* in (5.20) and Theorem 5.12 → ρ* = inf_{f ∈ Π_SSR} ∫ c dη̂(f) (p. 312); reason: the paper's definition; it is the sample path optimal cost of f₀
--   - encoding: (c) and (d) under every π ∈ Π and μ ∈ 𝒫(S), conditionally on 𝔉_t → one-step inequalities for every state–action pair; Z represented by its law ζ on ℝ; reason: the conditional statements depend only on (X_t, A_t) and every pair occurs under some π and μ, so the forms are equivalent
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 314, Theorem 5.12, (5.20) and Assumption 5.21; p. 312, Assumption 5.18 and ρ*

import Mathlib
import Definitions.Def_ArapostathisAC_VanishingDiscount_CMP
import Definitions.Def_ArapostathisAC_VanishingDiscount_StationaryChain
import Definitions.Def_ArapostathisAC_VanishingDiscount_Supplement_Occupation
import Definitions.Def_ArapostathisAC_VanishingDiscount_Supplement_Uniqueness

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open ArapostathisAC.VanishingDiscount

namespace ArapostathisAC.VanishingDiscount.Supplement

/-- Theorem 5.12 (p. 314), under the standing assumptions of §5.3. Let `f₀ ∈ Π_SD` be sample path
average cost optimal, with `E^{f₀}_i[τ] < ∞` and `E^{f₀}_i[∑_{t<τ} c] < ∞` for every `i`
(`τ = min {t ≥ 1 : X_t = 0}`), let `ρ* = inf_{f ∈ Π_SSR} ∫ c dη̂(f)` and let `h` be given by (5.20).
(1) Under Assumption 5.18 (and the stability under local perturbations, Assumption 5.21, under
which (5.20) solves the ACOE): with `H = {(ρ, w) : ACOE, w(0) = 0, inf w > −∞}`, `(ρ*, h) ∈ H`, and
every `(ρ', w') ∈ H` has `ρ' ≥ ρ*`, with equality iff `w' = h`.
(2) If instead `c` is bounded and the Lyapunov condition (a)–(d) holds for `W`, `B`, `ε`, then
`(ρ*, h)` is the unique solution of the ACOE in the class `{(ρ, u) : u(0) = 0,
limsup_{i→∞} u(i)/W(i) < ∞}`. -/
theorem theorem_5_12 {A : Type*} [MetricSpace A] [CompactSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (hstd : StandingConvex M)
    (f₀ : StationaryPolicy M) (hf₀ : IsSamplePathOptimalIn M Set.univ f₀.toPolicy)
    (hτ : ∀ i, meanReturn0 M f₀ i ≠ ⊤) (hcτ : ∀ i, costToReturn M f₀ i ≠ ⊤) :
    (Assumption518 M → Assumption521 M →
      (ACOE M (rhoStar M).toReal (returnPotential M f₀ (rhoStar M).toReal) ∧
        returnPotential M f₀ (rhoStar M).toReal 0 = 0 ∧
        BddBelow (Set.range (returnPotential M f₀ (rhoStar M).toReal))) ∧
      ∀ (ρ' : ℝ) (w' : ℕ → ℝ), ACOE M ρ' w' → w' 0 = 0 → BddBelow (Set.range w') →
        (rhoStar M).toReal ≤ ρ' ∧
          (ρ' = (rhoStar M).toReal ↔ w' = returnPotential M f₀ (rhoStar M).toReal)) ∧
    ((∃ C : ℝ, ∀ i, ∀ a ∈ M.U i, M.c i a ≤ C) →
      ∀ (W : ℕ → ℝ) (B : Set ℕ) (ε : ℝ), Lyapunov512 M W B ε →
      (ACOE M (rhoStar M).toReal (returnPotential M f₀ (rhoStar M).toReal) ∧
        returnPotential M f₀ (rhoStar M).toReal 0 = 0 ∧
        IsBoundedUnder (· ≤ ·) atTop
          (fun i => returnPotential M f₀ (rhoStar M).toReal i / W i)) ∧
      ∀ (ρ : ℝ) (u : ℕ → ℝ), ACOE M ρ u → u 0 = 0 →
        IsBoundedUnder (· ≤ ·) atTop (fun i => u i / W i) →
        ρ = (rhoStar M).toReal ∧ u = returnPotential M f₀ (rhoStar M).toReal) := by sorry

end ArapostathisAC.VanishingDiscount.Supplement
