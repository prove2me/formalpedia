-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_bv_fixedTime_scale_integrable_of_root_no_standing
-- name    : AvramDividend.Classical.p2m81_bv_fixedTime_scale_integrable_of_root_no_standing
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T05:13:00.594532+00:00
-- url     : https://prove2.me/theorems/754ff2e3-17ea-45c9-92b1-a204f8e9e40b
-- title:
--   Fixed-time q-scale integrability from positive Esscher root without standing (public)
-- statement:
--   A positive right root phi of the Laplace exponent with psi(phi)=q supplies an exponential gap dominating the q-scale function, so W(x+X_t) is integrable at any fixed time without any Standing assumption.
-- source:
--   Public mirror of the statement of private Proved Kyprianou.Ch08.StageB.positiveRoot_fixedTime_scale_integrable (0b4c9214), which public targets cannot import. Proof replays its accepted mathematical argument from three public lemmas only: levy_psi_root_shifted_increment_lower (e9488750), chat03_scale_global_weighted_exponential_bound (8c6ea1c8), chat03_scale_function_borel_measurable (45cbe3b4). Serves parent H1 (ee75bf61) fixed-time leg and any public child needing it.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.p2m81_bv_fixedTime_scale_integrable_of_root_no_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P F)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (t : ℝ≥0) :
    Integrable (fun ω => W (x + X.X t ω)) P := by sorry
