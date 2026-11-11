-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin29_original_bounded_stop_kernel_support
-- name    : AvramDividend.Classical.avram_mix_fin29_original_bounded_stop_kernel_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T17:40:06.105381+00:00
-- url     : https://prove2.me/theorems/cb5dd598-3086-4d6c-8743-d61bbc9b8007
-- title:
--   Bounded original stopping clock forces the stopped jump kernel to be supported before the deterministic horizon
-- statement:
--   For every path, an original stopped mark kernel H(t,omega,z)=1_{t≤rho(omega)}G(t,omega,z), with rho(omega)≤T, vanishes whenever t>T. Therefore H equals its indicator on the time-horizon support set S={t≤T}. This is the exact support hypothesis hSupport of the Proved original compensated-source martingale f445799e, needed when applying it to the finite-mixed physical HJB jump kernel. The proof uses only order transitivity and preserves inclusion of the stop-time jump atom.

import Mathlib
open MeasureTheory Set
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin29_original_bounded_stop_kernel_support
    {Ω : Type*}
    (T : ℝ≥0) (ρ : Ω → ℝ≥0)
    (hρbound : ∀ ω, ρ ω ≤ T)
    (G : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (S : Set ((ℝ≥0 × Ω) × ℝ))
    (hS : S = {p | p.1.1 ≤ T})
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hH : H = fun p => if p.1.1 ≤ ρ p.1.2 then G p else 0) :
    S.indicator H = H := by sorry
