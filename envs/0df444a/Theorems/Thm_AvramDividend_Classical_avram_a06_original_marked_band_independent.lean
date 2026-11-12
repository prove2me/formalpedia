-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_marked_band_independent
-- name    : AvramDividend.Classical.avram_a06_original_marked_band_independent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T00:55:49.221629+00:00
-- url     : https://prove2.me/theorems/2a80927e-56fc-473a-b62f-32bd67fa1f9b
-- title:
--   Original exponential-renewal marked arrival-band sums on disjoint cells are independent
-- statement:
--   For every deterministic monotone finite time grid, the original-space mark sums between successive arrival counts form an independent family. This is the source-specific independent-marked-Poisson-band theorem, with no auxiliary probability-space substitution.
-- source:
--   Original driver has jointly independent Exp(1) interarrivals and uniform negative marks; finite marked-Poisson arrival bands.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_piecewisePath
import Definitions.Def_levy_foundations_jumpCount
import Definitions.Def_LeanLevy_Processes_StochasticProcess
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical Filter Finset
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_marked_band_independent
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0) (ht : Monotone t),
      iIndepFun (fun (i : Fin n) ω =>
        ∑ j ∈ Finset.Ico
          (LevyFoundations.jumpCount
            (fun k => LevyFoundations.arrival τ k ω) (t i.castSucc : ℝ))
          (LevyFoundations.jumpCount
            (fun k => LevyFoundations.arrival τ k ω) (t i.succ : ℝ)),
        Y j ω) P := by sorry
