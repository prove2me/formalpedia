-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_i_original_stopped_discounted_fixed_mark_taylor_left_mesh_converges
-- name    : AvramDividend.Classical.avram_p4_s3_interval_i_original_stopped_discounted_fixed_mark_taylor_left_mesh_converges
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:18:51.812255+00:00
-- url     : https://prove2.me/theorems/e8545f23-585a-47ea-a886-6fc28815e6fd
-- title:
--   Actual original inclusive-stopped discounted nonlinear Taylor fixed-mark kernel left-mesh consistency
-- statement:
--   For the same original controlled X/D and genuine right-continuous stopping time τ, any deterministic mesh approaching t from the left yields convergence of the discounted nonlinear fixed-mark Taylor kernel multiplied by the inclusive physical clock indicator 1_{s≤τ}. The inclusive indicator is left-continuous even at t=τ. Local continuity of w at Y and Y+z, and of deriv w at Y, is explicit. This gives a pathwise source-exact predictable simple approximation of the correctly stopped derivative-driven Itô–Meyer kernel at each fixed real mark, without an L¹ or ν-tail claim.
-- source:
--   Use the Proved original pre-jump nonlinear fixed-mark Taylor mesh convergence and continuity of the exponential discount. For the inclusive physical stopping indicator 1_{s≤τ}, prove left-mesh convergence by t≤τ (all s_n≤τ) or τ<t (eventual s_n>τ by Tendsto into the open right ray). Multiply the three limits. This carefully distinguishes the discontinuous strict indicator 1_{s<τ} at t=τ and avoids unjustified stopped terminal atom passage.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_i_original_prejump_fixed_mark_taylor_mesh_converges
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_interval_i_original_stopped_discounted_fixed_mark_taylor_left_mesh_converges
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (ω : Ω) (t : ℝ≥0)
    (s : ℕ → ℝ≥0) (hsle : ∀ n, s n ≤ t)
    (hst : Tendsto s atTop (𝓝 t))
    (w : ℝ → ℝ) (q z : ℝ)
    (hwy : ContinuousAt w (Function.leftLim
      (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) t))
    (hwyz : ContinuousAt w (Function.leftLim
      (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) t + z))
    (hder : ContinuousAt (deriv w) (Function.leftLim
      (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) t)) :
    let K : ℝ≥0 → ℝ := fun u =>
      Real.exp (-(q * (u : ℝ))) *
        ((fun y : ℝ => w (y + z) - w y - z * deriv w y)
          (Function.leftLim
            (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u))
    Tendsto
      (fun n => (if s n ≤ τ ω then (1 : ℝ) else 0) * K (s n))
      atTop
      (𝓝 ((if t ≤ τ ω then (1 : ℝ) else 0) * K t)) := by sorry
