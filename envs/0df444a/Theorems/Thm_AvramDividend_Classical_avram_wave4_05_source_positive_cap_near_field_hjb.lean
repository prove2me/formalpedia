-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_positive_cap_near_field_hjb
-- name    : AvramDividend.Classical.avram_wave4_05_source_positive_cap_near_field_hjb
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:25:16.826551+00:00
-- url     : https://prove2.me/theorems/1fb2ce01-4281-4899-aebf-b08c412941bb
-- title:
--   Sharp source near-field HJB above a positive optimal barrier under Standing alone
-- statement:
--   Let X be the genuine spectrally negative Levy process satisfying Standing, q>0, W its q-scale function, and a>0 the real optimal barrier. At every reserve x>a with x>=1 and x>=a+max(0,c/q), the original fully compensated Levy generator of the barrier candidate exists and the exact HJB max of generator residual and the dividend gradient residual is zero. In particular jumps with -1<y<0 may cross the barrier, yet their compensated contribution is nonpositive by the left affine majorant obtained from the already Proved source derivative inequality v'>=1 and the actual source continuity at zero. The source jump-integrability and the sharp drift threshold are supplied by the Proved near-field affine-majorant HJB bridge. This genuine source result removes all extra affine-majorant, regular scale positivity, and global C1 assumptions from the near-field bridge, and reduces the previous far-field reserve threshold by one unit.
-- source:
--   Avram, Palmowski and Pistorius (2007), Theorem 2(ii), equation (5.8) and Lemma 3(i); original SpectrallyNegativeLevy.generator, genuine source gradient vcstar_deriv_ge_one, compact lower-branch continuity vcstar_continuousOn_Icc_below_positive_cstar, mathematical mean-value lemma left_affine_majorant_of_deriv_ge_one and Proved near-field compensated generator HJB vcstar_near_HJB_of_affine_majorant_at_threshold. This is a source-analytic strengthening of Chat 05's Proved far-field result and is independent of Chat 06's stochastic optional-stopping tasks.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_positive_cap_near_field_hjb {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (hpos : 0 < (cstar W).toReal) (x : ℝ) (hx : (cstar W).toReal < x) (hx1 : 1 ≤ x) (hthreshold : (cstar W).toReal + max 0 (X.c / q) ≤ x) : X.GeneratorIntegrable (vcstar W) x ∧ max (X.generator (vcstar W) x - q * vcstar W x) (1 - deriv (vcstar W) x) = 0 := by sorry
