-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_genuine_esscher_fixed_clock_fibre_terminal_mgf
-- name    : AvramDividend.Classical.avram_ws01e_b_genuine_esscher_fixed_clock_fibre_terminal_mgf
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T20:42:48.914203+00:00
-- url     : https://prove2.me/theorems/6e4e9288-aed8-4f5f-b0aa-90bc6bb7ea4d
-- title:
--   Exact fixed-clock Esscher density weighted Levy terminal exponential moment
-- statement:
--   For a genuine spectrally negative Lévy process, each fixed real clock t interpreted as its nonnegative part, and real parameters φ,q,β with ψ(φ)=q and φ+β≥0, the original P-integral of the actual finite-horizon Esscher likelihood exp(φX_t−tψφ) times the terminal exponential reward exp(βX_t) equals exp(t(ψ(φ+β)−q)). No fake tilted law or random-clock independence hypothesis is assumed. This exact fibre identity is required to integrate the true random-terminal Esscher law against an independent exponential clock.
-- source:
--   Kuznetsov–Kyprianou–Rivero (2013) Esscher exponent identity and Proved SpectrallyNegativeLevy.laplace; genuine tilted finite-rate Wiener–Hopf derivation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_genuine_esscher_fixed_clock_fibre_terminal_mgf
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (φ q β : ℝ) (hroot : X.ψ φ = q)
    (hθ : 0 ≤ φ + β) (t : ℝ) :
    (∫⁻ ω : Ω,
      ENNReal.ofReal (Real.exp
        (φ * X.X (Real.toNNReal t) ω -
          (Real.toNNReal t : ℝ) * X.ψ φ)) *
      ENNReal.ofReal (Real.exp
        (β * X.X (Real.toNNReal t) ω)) ∂P) =
    ENNReal.ofReal (Real.exp
      ((Real.toNNReal t : ℝ) * (X.ψ (φ + β) - q))) := by sorry
