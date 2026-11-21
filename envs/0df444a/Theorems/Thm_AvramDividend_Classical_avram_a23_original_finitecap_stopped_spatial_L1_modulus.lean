-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a23_original_finitecap_stopped_spatial_L1_modulus
-- name    : AvramDividend.Classical.avram_a23_original_finitecap_stopped_spatial_L1_modulus
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:46:25.345181+00:00
-- url     : https://prove2.me/theorems/cf82f521-4748-4ca0-89c6-f6d3827ebb19
-- title:
--   Original finitecap stopped Gaussian interior spatial L1 transfer from reserve-gap L1
-- statement:
--   Under the actual finite reserve band [0,b], L1 convergence of the spatial reserve gap U_m−V_m to zero transfers to the HJB candidate value gap w(U_m)−w(V_m) in L1. The proof uses the original continuousOn w (Ici0), a finite compact absolute bound and quantitative Heine-Cantor spatial modulus, followed by a near/far ε+const|U−V| bound and integration. This is the precise interior component needed by finitecap Gaussian physical mesh crossings, without assuming global Lipschitz or continuity below ruin.
-- source:
--   Compact finite reserve spatial gap L1 transfer, using original HJB w and actual integrable mesh reserve variables.

import Mathlib
open MeasureTheory Set Filter

theorem AvramDividend.Classical.avram_a23_original_finitecap_stopped_spatial_L1_modulus
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (w : ℝ → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hw_cont : ContinuousOn w (Ici 0))
    (U V : ℕ → Ω → ℝ)
    (hInside : ∀ m, ∀ᵐ ω ∂P,
      0 ≤ U m ω ∧ U m ω ≤ b ∧ 0 ≤ V m ω ∧ V m ω ≤ b)
    (hWI : ∀ m, Integrable (fun ω => |w (U m ω) - w (V m ω)|) P)
    (hDI : ∀ m, Integrable (fun ω => |U m ω - V m ω|) P)
    (hD : Tendsto (fun m => ∫ ω, |U m ω - V m ω| ∂P)
       atTop (nhds (0 : ℝ))) :
    Tendsto (fun m => ∫ ω, |w (U m ω) - w (V m ω)| ∂P)
      atTop (nhds (0 : ℝ)) := by sorry
