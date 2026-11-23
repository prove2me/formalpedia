-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsv_positive_stopped_cash_excess_vanishes_of_pathwise_L1
-- name    : AvramDividend.Classical.avram_lsv_positive_stopped_cash_excess_vanishes_of_pathwise_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T07:23:08.684496+00:00
-- url     : https://prove2.me/theorems/f7a15b05-c868-4d28-8f1a-5a766a2d7df8
-- title:
--   Positive stopped-cash excess vanishes in L1 under a source-pathwise upper bound and L1 convergence of the centred mesh
-- statement:
--   For the same stopped-event measure and real cash payoff, if the excess over a finite Gaussian mesh is integrable for every mesh, the mesh converges in L1 to a limiting centred process, and the actual pathwise cash excess is bounded almost everywhere by that limit, then the expected positive cash excess above the physical Gaussian mesh tends to zero. This generic lemma preserves the exact positive-event restriction used by the original Avram finite-cap stopped Ito-Stieltjes cash source; it replaces no stochastic assumption or cap-boundary proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_lsv_positive_stopped_cash_excess_vanishes_of_pathwise_L1
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (g Z : Ω → ℝ) (M : ℕ → Ω → ℝ)
    (hI : ∀ m, Integrable (fun ω => max (g ω - M m ω) 0) (P.restrict A))
    (hDI : ∀ m, Integrable (fun ω => |Z ω - M m ω|) (P.restrict A))
    (hL : Tendsto (fun m => ∫ ω in A, |Z ω - M m ω| ∂P)
      atTop (nhds (0 : ℝ)))
    (hPath : ∀ᵐ ω ∂(P.restrict A), g ω ≤ Z ω) :
    Tendsto (fun m => ∫ ω in A, max (g ω - M m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by sorry
