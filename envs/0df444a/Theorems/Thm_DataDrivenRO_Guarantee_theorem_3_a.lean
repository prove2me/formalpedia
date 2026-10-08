-- Prove2me | Theorems.Thm_DataDrivenRO_Guarantee_theorem_3_a
-- name    : DataDrivenRO.Guarantee.theorem_3_a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T13:42:58.644989+00:00
-- url     : https://prove2.me/theorems/eb15cdbf-7aa9-4de8-bd5e-b5c5551beee6
-- title:
--   Theorem 3(a), p. 12 — if 𝒫(𝒮,α) does not depend on ε, w.p. ≥ 1 − α the family {𝒰(𝒮,ε,α)} simultaneously implies a guarantee
-- statement:
--   Fix $0<\alpha<1$. Data $\mathcal S=(\hat{\mathbf u}^1,\dots,\hat{\mathbf u}^N)$ are drawn i.i.d. from $\mathbb P^*$ on $\mathbb R^d$. Suppose the confidence region $\mathcal P(\mathcal S)$ of Step 1 does not depend on $\epsilon$ and satisfies $\mathbb P^*_{\mathcal S}(\mathbb P^*\in\mathcal P(\mathcal S))\ge1-\alpha$, and that for every $0<\epsilon<1$ the set $\mathcal U(\mathcal S,\epsilon)$ is nonempty, convex and compact with
--   $$\mathrm{VaR}^{\mathbb P}_\epsilon(\mathbf v)\le\delta^*\big(\mathbf v\mid\mathcal U(\mathcal S,\epsilon)\big)\qquad\forall\,\mathbb P\in\mathcal P(\mathcal S),\ \forall\,\mathbf v\in\mathbb R^d .$$
--   Then
--   $$\mathbb P^*_{\mathcal S}\big(\{\mathcal U(\mathcal S,\epsilon):0<\epsilon<1\}\text{ simultaneously implies a probabilistic guarantee for }\mathbb P^*\big)\ge1-\alpha .$$
--
--   Because the event does not depend on a single level, the levels $\epsilon$ may be chosen after seeing the data, which Theorem 2 does not allow. This is what justifies optimizing the levels $\epsilon_j$ in (9).
--
--   **Formalization Note** Same encoding as Theorem 2: the family is a map $(\mathcal S,\epsilon)\mapsto\mathcal U(\mathcal S,\epsilon)$, constrained only for $\epsilon\in(0,1)$; coverage is a hypothesis; Step 2 uses $g=\delta^*$ directly.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, definition p. 11 and Theorem 3(a), pp. 11–12 (proof EC.1.2, pp. ec1–ec2)

import Mathlib
import Definitions.Def_DataDrivenRO_Guarantee_Setting

open MeasureTheory

namespace DataDrivenRO.Guarantee

/-- Theorem 3(a), p. 12 (proof EC.1.2, pp. ec1–ec2). Data `S` are drawn i.i.d. from `ℙ*`. The
confidence region `𝒫(S)` does not depend on `ε` and contains `ℙ*` with probability at least
`1 − α`; for every `0 < ε < 1`, `U(S, ε)` is nonempty, convex and compact, and its support
function bounds the level-`ε` Value at Risk of every probability measure in `𝒫(S)`. Then, with
probability at least `1 − α` with respect to the sampling, the family `{U(S, ε) : 0 < ε < 1}`
simultaneously implies a probabilistic guarantee for `ℙ*`. -/
theorem theorem_3_a {d N : ℕ} (Pstar : Measure (Fin d → ℝ)) [IsProbabilityMeasure Pstar]
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (region : (Fin N → Fin d → ℝ) → Set (Measure (Fin d → ℝ)))
    (U : (Fin N → Fin d → ℝ) → ℝ → Set (Fin d → ℝ))
    (hne : ∀ S, ∀ ε ∈ Set.Ioo (0 : ℝ) 1, (U S ε).Nonempty)
    (hconv : ∀ S, ∀ ε ∈ Set.Ioo (0 : ℝ) 1, Convex ℝ (U S ε))
    (hcpt : ∀ S, ∀ ε ∈ Set.Ioo (0 : ℝ) 1, IsCompact (U S ε))
    (hstep2 : ∀ S, ∀ ε ∈ Set.Ioo (0 : ℝ) 1, ∀ P ∈ region S, IsProbabilityMeasure P →
      ∀ v, VaR P ε v ≤ RobustMDP.Shared.supportFunction (U S ε) v)
    (hcover : ENNReal.ofReal (1 - α) ≤
      Measure.pi (fun _ : Fin N => Pstar) {S | Pstar ∈ region S}) :
    ENNReal.ofReal (1 - α) ≤
      Measure.pi (fun _ : Fin N => Pstar) {S | SimultaneouslyImpliesGuarantee Pstar (U S)} := by sorry

end DataDrivenRO.Guarantee
