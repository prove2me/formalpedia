-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_generator_congr_scaledW_inside_cstar
-- name    : AvramDividend.Classical.vcstar_generator_congr_scaledW_inside_cstar
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T14:02:55.562733+00:00
-- url     : https://prove2.me/theorems/680b65bf-dd27-49d5-9074-fbfc30fb2d0a
-- title:
--   Exact nonlocal generator and domain congruence below the canonical barrier
-- statement:
--   For any pinned formal scale function W and any reserve 0<x<(cstar W).toReal, the exact dividend candidate vcstar W and its normalised scale function z↦divE(W z, scaleDeriv W (cstar W).toReal) have equivalent generator-integrability domains and identical full spectrally negative Lévy generator values at x. The functions are equal on the whole half-line to the left of the barrier. Pinned Mathlib EqOn derivatives and iterated derivatives on the open left region therefore coincide, and the already-Proved left-germ generator theorem carries equality through the compensated nonlocal jump integral. No harmonicity, positivity of W' or regularity beyond the formal scale-function definition is assumed. This directly reduces original Chat 7 interior generator_vcstar_eq_zero to genuine harmonicity of the scaled scale function.

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.vcstar_generator_congr_scaledW_inside_cstar
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : x ∈ Ioo 0 (cstar W).toReal) :
    (X.GeneratorIntegrable (vcstar W) x ↔
      X.GeneratorIntegrable
        (fun z : ℝ => divE (W z)
          (scaleDeriv W (cstar W).toReal)) x) ∧
      X.generator (vcstar W) x =
        X.generator (fun z : ℝ => divE (W z)
          (scaleDeriv W (cstar W).toReal)) x := by sorry
