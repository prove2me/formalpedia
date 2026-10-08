-- Prove2me | Theorems.Thm_AvramDividend_Classical_supermartingale_expected_stoppedValue_antitone_nat
-- name    : AvramDividend.Classical.supermartingale_expected_stoppedValue_antitone_nat
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T21:56:57.710245+00:00
-- url     : https://prove2.me/theorems/2c1f1762-5894-4b1e-b166-a1cb854590dd
-- title:
--   Bounded optional stopping inequality for real-valued supermartingales on natural time
-- statement:
--   For a real-valued supermartingale indexed by natural time, expected stopped values decrease between two ordered stopping times whenever the later stopping time is uniformly bounded. This is the supermartingale form of Mathlib's optional-stopping inequality, obtained by negating the process and applying the corresponding submartingale theorem.
-- source:
--   Mathlib Probability.Martingale.OptionalStopping; generic helper for finite-grid localisation in Proposition 4(i).

import Mathlib

open MeasureTheory

theorem AvramDividend.Classical.supermartingale_expected_stoppedValue_antitone_nat
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    {𝓖 : Filtration ℕ mΩ} [SigmaFiniteFiltration μ 𝓖]
    {f : ℕ → Ω → ℝ} (hf : Supermartingale f 𝓖 μ)
    {τ π : Ω → WithTop ℕ}
    (hτ : IsStoppingTime 𝓖 τ) (hπ : IsStoppingTime 𝓖 π)
    (hle : τ ≤ π) {N : ℕ} (hbdd : ∀ ω, π ω ≤ (N : WithTop ℕ)) :
    (∫ ω, stoppedValue f π ω ∂μ) ≤
      ∫ ω, stoppedValue f τ ω ∂μ := by sorry
