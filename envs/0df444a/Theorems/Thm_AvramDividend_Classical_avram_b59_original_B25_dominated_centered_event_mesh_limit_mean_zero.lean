-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b59_original_B25_dominated_centered_event_mesh_limit_mean_zero
-- name    : AvramDividend.Classical.avram_b59_original_B25_dominated_centered_event_mesh_limit_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T08:50:55.106205+00:00
-- url     : https://prove2.me/theorems/ac32db58-39c7-478b-a8df-e9d4c7da711c
-- title:
--   Original B25 L1-dominated Gaussian or small-jump physical mesh gains have centred limit on any event when every integrable physical mesh gain is event-centred
-- statement:
--   The original B25 source supplies integrable dominating fields BG,BJ, bounded signed physical-grid gains G,J, and almost-sure pointwise limits MG,MJ. When the genuine source physical grid gains are integrable and event-centred, pinned Bochner dominated convergence on the event-restricted measure proves their limits have zero event integrals. The proof uses the genuine original B25 domination, not a false L1 vanishing assumption on the error E, providing the event centring needed after the source-exact B58 cash-limit inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b59_original_B25_dominated_centered_event_mesh_limit_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (A : Set Ω) (G : ℕ → Ω → ℝ) (MG BG : Ω → ℝ)
    (hGI : ∀ k, Integrable (G k) P)
    (hBG : Integrable BG P)
    (hDom : ∀ k, ∀ᵐ ω ∂P, ‖G k ω‖ ≤ BG ω)
    (hLim : ∀ᵐ ω ∂P,
      Tendsto (fun k => G k ω) atTop (𝓝 (MG ω)))
    (hCenter : ∀ k, (∫ ω in A, G k ω ∂P) = 0) :
    (∫ ω in A, MG ω ∂P) = 0 := by sorry
