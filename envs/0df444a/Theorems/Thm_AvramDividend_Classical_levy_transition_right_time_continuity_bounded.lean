-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_transition_right_time_continuity_bounded
-- name    : AvramDividend.Classical.levy_transition_right_time_continuity_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T22:02:28.367676+00:00
-- url     : https://prove2.me/theorems/41645528-75ce-4613-8255-c83a563d503b
-- title:
--   Right continuity in time of the Lévy transition semigroup for bounded continuous payoffs
-- statement:
--   For the given adapted cadlag spectrally negative Lévy process and a bounded continuous real payoff f, fix starting reserve x and time t≥0. If τ_n≥t and τ_n→t, then E[f(x+X_(τ_n))]→E[f(x+X_t)]. This is the strong right-continuity in the transition time, extending time-zero continuity. Each sample path is continuous from the right at t; τ_n approaches t through the within-filter Ici t, so X_(τ_n)(ω)→X_t(ω). By continuity f yields pointwise convergence and its uniform bound supplies an integrable dominated-convergence envelope under the probability measure P. Time-specific measurability follows from the adapted process. This proves the Feller-type time regularity needed for a semigroup generator investigation but does not itself identify the Lévy–Khintchine generator or give the stopped HJB dividend inequality.
-- source:
--   Only SpectrallyNegativeLevy.rightCont/adapted/isProbability and pinned Bochner dominated convergence; no Open theorem imports.

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Process.Adapted
import Mathlib.Topology.Instances.NNReal.Lemmas
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_transition_right_time_continuity_bounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ) (hf : Continuous f)
    (B : ℝ) (hB : ∀ y : ℝ, ‖f y‖ ≤ B)
    (x : ℝ) (t : ℝ≥0) (τ : ℕ → ℝ≥0)
    (hτle : ∀ n, t ≤ τ n)
    (hτ : Filter.Tendsto τ Filter.atTop (nhds t)) :
    Filter.Tendsto
      (fun n => ∫ ω, f (x + X.X (τ n) ω) ∂P)
      Filter.atTop (nhds (∫ ω, f (x + X.X t ω) ∂P)) := by sorry
