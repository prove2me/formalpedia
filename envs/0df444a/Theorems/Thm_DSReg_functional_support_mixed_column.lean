-- Prove2me | Theorems.Thm_DSReg_functional_support_mixed_column
-- name    : DSReg.functional_support_mixed_column
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:27:48.496769+00:00
-- url     : https://prove2.me/theorems/41435f67-9e95-4e0a-93e5-fb76f7bc0f96
-- title:
--   Lemma 2: functional support of a mixed column
-- statement:
--   Let $x=g(z)$, with $g$ differentiable $\mu$-a.e. and measurable Jacobian $D$, and let $D$ satisfy Functional no-cancellation (Assumption 2). Let $U\in O(d)$, fix a column $j$, and put $\mathcal I_j=\{i:U_{ij}\ne0\}$. Then the a.e. support of the $j$-th column of $D(\cdot)U$ is the union of the footprints of the latents it mixes:
--
--   $$\operatorname{supp}_\mu\big((D(\cdot)U)_{:,j}\big)=\bigcup_{i\in\mathcal I_j}\mathcal S_i.$$
-- source:
--   Zheng, Klindt, Balestriero and Schölkopf, DSReg: Provably Recovering Individual World Latents without Reconstruction, arXiv:2610.09457v1 (2026), Appendix A.2, Lemma 2, p. 17

import Mathlib
import Definitions.Def_DSReg_Basic

open MeasureTheory

namespace DSReg

theorem functional_support_mixed_column {d p : ℕ} (μ : Measure (Fin d → ℝ))
    [IsProbabilityMeasure μ] (g : (Fin d → ℝ) → Fin p → ℝ)
    (hdiff : ∀ᵐ z ∂μ, DifferentiableAt ℝ g z) (hmeas : ∀ r i, Measurable fun z => depJac g z r i)
    (hfnc : FunctionalNoCancellation μ (depJac g))
    (U : Matrix (Fin d) (Fin d) ℝ) (hU : U ∈ Matrix.orthogonalGroup (Fin d) ℝ) (j : Fin d) :
    aeSupport μ (fun z r => (depJac g z * U) r j) =
      ⋃ i ∈ {i : Fin d | U i j ≠ 0}, footprint μ (depJac g) i := by sorry

end DSReg
