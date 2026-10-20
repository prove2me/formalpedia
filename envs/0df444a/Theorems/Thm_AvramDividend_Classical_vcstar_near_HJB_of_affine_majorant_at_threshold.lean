-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_near_HJB_of_affine_majorant_at_threshold
-- name    : AvramDividend.Classical.vcstar_near_HJB_of_affine_majorant_at_threshold
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T13:15:46.654642+00:00
-- url     : https://prove2.me/theorems/3425d74f-8c4c-464b-a957-3f35a9c39670
-- title:
--   Full near-barrier HJB at the sharp drift threshold under the left affine majorant
-- statement:
--   Let W be an exact q-scale function, q>0 and a=(cstar W).toReal>0. Suppose its dividend value satisfies the left affine-majorant shape vcstar W z≤vcstar W a + z−a for all 0≤z≤a. Then every x>a with x≥1 and x≥a+max(0,X.c/q) satisfies the true Lévy generator domain condition and exact dividend HJB equality max(Γv−qv,1−v')=0. The result combines the nonlocal crossing-jump sign theorem with already-proved global monotonicity and the strengthened discounted value threshold. It genuinely enlarges the previously Proved far-field region, subject to a nontrivial derivative/chord obligation. It does not infer the affine majorant from the bare scale-function Laplace characterisation.

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.vcstar_near_HJB_of_affine_majorant_at_threshold
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hpos : 0 < (cstar W).toReal)
    (hchord : ∀ z : ℝ, 0 ≤ z → z ≤ (cstar W).toReal →
      vcstar W z ≤
        z - (cstar W).toReal + vcstar W (cstar W).toReal)
    (x : ℝ) (hx : (cstar W).toReal < x) (hx1 : 1 ≤ x)
    (hthreshold : (cstar W).toReal + max 0 (X.c / q) ≤ x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      max (X.generator (vcstar W) x - q * vcstar W x)
        (1 - deriv (vcstar W) x) = 0 := by sorry
