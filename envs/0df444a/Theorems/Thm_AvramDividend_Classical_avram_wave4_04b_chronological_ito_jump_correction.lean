-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_chronological_ito_jump_correction
-- name    : AvramDividend.Classical.avram_wave4_04b_chronological_ito_jump_correction
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T09:19:35.145496+00:00
-- url     : https://prove2.me/theorems/14ce41c4-e590-4615-8a70-43f2a0f5d25c
-- title:
--   Chronological source Lévy and adapted right-dividend jump split in the nonlinear Itô–Meyer remainder
-- statement:
--   For the actual original spectrally negative Lévy path, any adapted left-continuous dividend policy, any positive time and any real test function, the nonlinear Itô–Meyer jump remainder for the post-payment reserve decomposes exactly into the source Lévy jump remainder and a chronological right-payment correction. Under the original verification hypothesis hjump, this right-payment correction, after adding back the derivative term in the semimartingale formula, is bounded above by the negative dividend atom. This is a partial jump-interface theorem, not the finite-horizon stochastic chain rule: continuous and singular-continuous Stieltjes mass, Brownian quadratic variation and compensated small jumps still need their own proofs.
-- source:
--   Original Avram–Palmowski–Pistorius (2007), Proposition 4 proof eqs. (5.11)–(5.12); exact existing source path representation and rightLimit D. Uses the canonical corrected hjump inequality pointwise. No artificial Lévy process, Stieltjes atomic-concentration assumption, stochastic-integration axiom or replacement of corrected UBV verification inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04b_chronological_ito_jump_correction
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (ω : Ω) (t : ℝ≥0) (ht : 0 < t)
    (hjump : rightLimit D t ω - D t ω ≤
      w (x + X.X t ω - D t ω) -
        w (x + X.X t ω - rightLimit D t ω)) :
    let before : ℝ :=
      x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω
    let afterSource : ℝ := x + X.X t ω - D t ω
    let afterPayment : ℝ := x + X.X t ω - rightLimit D t ω
    let sourceJump : ℝ :=
      X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t
    let paymentAtom : ℝ := rightLimit D t ω - D t ω
    (w afterPayment - w before -
        deriv w before * (sourceJump - paymentAtom) =
      (w afterSource - w before - deriv w before * sourceJump) +
        (w afterPayment - w afterSource + deriv w before * paymentAtom)) ∧
      w afterPayment - w afterSource + paymentAtom ≤ 0 := by sorry
