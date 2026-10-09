-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_cstar_positive_boundary_regularity_package
-- name    : AvramDividend.Classical.scaleFunction_cstar_positive_boundary_regularity_package
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T17:18:42.59+00:00
-- url     : https://prove2.me/theorems/760663cc-d430-46ea-9b1d-84f245a65d50
-- title:
--   Canonical q-scale regularity and stationary derivative at the positive optimal barrier
-- statement:
--   Let X satisfy the source's standing conditions (3.3), q>0, and W be its q-scale function. At a finite positive minimising barrier c*, the scale function is differentiable on the positive half-line (the paper's C1 regularity under condition (3.3)), its derivative at c* is nonzero (strict positivity of the derivative for q>0), and in the nonzero-Gaussian case the derivative W' itself has derivative zero at the positive minimum. The latter uses Gaussian smoothness W∈C∞(0,∞) and Fermat's theorem applied to the minimiser of W'. These are the precise process-level inputs required by the already proved first- and second-derivative boundary smooth-fit calculus lemmas; no stochastic dividend verification inequalities are assumed.
-- source:
--   Avram–Palmowski–Pistorius (2007), §3.2 p.8 under condition (3.3): W is C1 and Gaussian W is C∞; §5.2 (5.2) and Lemma 2(i) for the minimising positive barrier. This synthesises the exact analytic input to target AvramDividend.Classical.vcstar_scaledW_boundary_smooth_fit, avoiding a long tangled import chain.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem scaleFunction_cstar_positive_boundary_regularity_package
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W) :
    (∀ y : ℝ, 0 < y → DifferentiableAt ℝ W y) ∧
    deriv W (cstar W).toReal ≠ 0 ∧
    (X.σ ≠ 0 → HasDerivAt (deriv W) 0 (cstar W).toReal) := by
  sorry

end AvramDividend.Classical
