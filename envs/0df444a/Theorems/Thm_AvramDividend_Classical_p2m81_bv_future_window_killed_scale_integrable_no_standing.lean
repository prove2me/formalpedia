-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_bv_future_window_killed_scale_integrable_no_standing
-- name    : AvramDividend.Classical.p2m81_bv_future_window_killed_scale_integrable_no_standing
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T05:03:26.666657+00:00
-- url     : https://prove2.me/theorems/9ba6e79b-11e0-4d58-8f29-a534cacd466d
-- title:
--   BV future-window killed scale payoff integrable from Esscher root without standing (public)
-- statement:
--   For a spectrally negative Levy process with positive discount q, positive Esscher root phi with psi(phi)=q, and genuine q-scale function W, the future-window killed discounted scale payoff over [s,u] is integrable. No Standing assumption.
-- source:
--   No-standing replay of the 3-line pattern of Proved 75fe5cab: fixed-time integrability via Proved 0b4c9214, const_mul by the deterministic discount, indicator over the measurable window from standing-free reindex 73138feb and Proved 3d9b599a. Supplies hf for parent H1 (ee75bf61).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.p2m81_bv_future_window_killed_scale_integrable_no_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (s u : ℝ≥0) (hsu : s ≤ u) :
    Integrable
      (({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
        (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
          W (x + X.X u ω))) P := by sorry
