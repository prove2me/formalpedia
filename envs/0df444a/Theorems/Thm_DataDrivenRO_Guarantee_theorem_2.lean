-- Prove2me | Theorems.Thm_DataDrivenRO_Guarantee_theorem_2
-- name    : DataDrivenRO.Guarantee.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T13:42:47.688896+00:00
-- url     : https://prove2.me/theorems/01013868-e73d-4807-b7b0-d2c26e029bac
-- title:
--   Theorem 2, p. 10 — w.p. ≥ 1 − α over the sample, the schema's set 𝒰(𝒮,ε,α) implies a probabilistic guarantee at level ε for ℙ*
-- statement:
--   Fix $0<\alpha<1$ and $0<\epsilon<1$. Data $\mathcal S=(\hat{\mathbf u}^1,\dots,\hat{\mathbf u}^N)$ are drawn i.i.d. from an unknown probability measure $\mathbb P^*$ on $\mathbb R^d$, and $\mathbb P^*_{\mathcal S}$ denotes the product law of the sample. The schema of §3.2 consists of
--
--   1. a confidence region $\mathcal P(\mathcal S)$ of a hypothesis test at level $\alpha$: $\mathbb P^*_{\mathcal S}\big(\mathbb P^*\in\mathcal P(\mathcal S)\big)\ge1-\alpha$;
--   2. a nonempty, convex, compact set $\mathcal U(\mathcal S)\subseteq\mathbb R^d$ whose support function bounds the worst-case Value at Risk over the region:
--   $$\sup_{\mathbb P\in\mathcal P(\mathcal S)}\mathrm{VaR}^{\mathbb P}_\epsilon(\mathbf v)\le\delta^*\big(\mathbf v\mid\mathcal U(\mathcal S)\big)\qquad\forall\,\mathbf v\in\mathbb R^d .$$
--
--   Then
--   $$\mathbb P^*_{\mathcal S}\big(\mathcal U(\mathcal S)\text{ implies a probabilistic guarantee at level }\epsilon\text{ for }\mathbb P^*\big)\ge1-\alpha .$$
--
--   Theorem 2 is the reason every set constructed in the paper carries a guarantee: the statistical work is the coverage of the test, the convex-analytic work is Step 2, and Theorem 1(a) connects them.
--
--   **Formalization Note** The sample is `S : Fin N → (Fin d → ℝ)` under `Measure.pi (fun _ => P*)`. The region and the set are arbitrary maps of the sample; coverage is a hypothesis, and the probabilities of possibly non-measurable events are outer measures. Steps 2–3 of the schema (a convex, positively homogeneous bound $g$ equal to $\delta^*(\cdot\mid\mathcal U(\mathcal S))$) are encoded with $g=\delta^*(\cdot\mid\mathcal U(\mathcal S))$ directly, as a bound on the VaR of every probability measure in the region. The paper's Step 3 says "closed, convex"; compactness and nonemptiness are assumed because $\delta^*(\cdot\mid\mathcal U)$ is finite and bounds VaR from above, which forces them, and because the published support function is a real supremum.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, schema of §3.2 and Theorem 2, p. 10 (proof EC.1.2, p. ec1)

import Mathlib
import Definitions.Def_DataDrivenRO_Guarantee_Setting

open MeasureTheory

namespace DataDrivenRO.Guarantee

/-- Theorem 2, p. 10 (proof EC.1.2, p. ec1). Data `S = (û¹, …, ûᴺ)` are drawn i.i.d. from `ℙ*`.
Let `𝒫(S)` be a confidence region that contains `ℙ*` with probability at least `1 − α`, and let
`U(S)` be a nonempty, convex, compact set whose support function bounds the Value at Risk of every
probability measure in the region (Steps 1–3 of the schema, with `g(v, S, ε, α) = δ*(v|U(S))`).
Then, with probability at least `1 − α` with respect to the sampling, `U(S)` implies a
probabilistic guarantee at level `ε` for `ℙ*`. -/
theorem theorem_2 {d N : ℕ} (Pstar : Measure (Fin d → ℝ)) [IsProbabilityMeasure Pstar]
    (α ε : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hε0 : 0 < ε) (hε1 : ε < 1)
    (region : (Fin N → Fin d → ℝ) → Set (Measure (Fin d → ℝ)))
    (U : (Fin N → Fin d → ℝ) → Set (Fin d → ℝ))
    (hne : ∀ S, (U S).Nonempty) (hconv : ∀ S, Convex ℝ (U S)) (hcpt : ∀ S, IsCompact (U S))
    (hstep2 : ∀ S, ∀ P ∈ region S, IsProbabilityMeasure P →
      ∀ v, VaR P ε v ≤ RobustMDP.Shared.supportFunction (U S) v)
    (hcover : ENNReal.ofReal (1 - α) ≤
      Measure.pi (fun _ : Fin N => Pstar) {S | Pstar ∈ region S}) :
    ENNReal.ofReal (1 - α) ≤
      Measure.pi (fun _ : Fin N => Pstar) {S | ImpliesGuarantee Pstar (U S) ε} := by sorry

end DataDrivenRO.Guarantee
