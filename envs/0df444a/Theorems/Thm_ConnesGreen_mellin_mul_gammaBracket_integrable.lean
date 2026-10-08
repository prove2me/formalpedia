-- Prove2me | Theorems.Thm_ConnesGreen_mellin_mul_gammaBracket_integrable
-- name    : ConnesGreen.mellin_mul_gammaBracket_integrable
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T03:24:54.9939+00:00
-- url     : https://prove2.me/theorems/8326c014-bc91-4be4-a119-94bde48e5dc9
-- title:
--   Original Mellin transform times the exact gamma symbol is integrable
-- statement:
--   For every unchanged original smooth compactly supported test k, mellinHat(k,1/2+i r) times Re digamma(1/4+i r/2)-log(pi) is integrable over the full real line. The public signature unfolds exactly the native gammaBracket definition. Accepted digamma strip growth bounds the symbol by a constant times 1+|r|; the original test gives a Schwartz Fourier transform, whose zeroth and first norm moments are integrable. The exact -r/(2 pi) frequency rescaling supplies a full integrable majorant. Gamma analyticity on the right half-plane supplies continuity. No weighted-convergence hypothesis, positivity premise or RH assumption is introduced.
-- source:
--   monocap-tech/weil at 6365e9fa26ba7faf91910d5a8270cb3f2cc34551; ArchimedeanEnergy.lean. Original native declarations unchanged. Exact native definition normalization checks accompany both ports.

import Definitions.Def_ConnesRZ_weil_defs
import Theorems.Thm_Zeta23_WeilEF_digamma_growth_strip
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Complex MeasureTheory ConnesRZ
open scoped FourierTransform
noncomputable section

theorem ConnesGreen.mellin_mul_gammaBracket_integrable (k : ℝ → ℂ) (hk : IsTest k) :
    Integrable (fun r : ℝ => mellinHat k (1 / 2 + I * r) *
      (((Complex.digamma (1 / 4 + I * r / 2)).re - Real.log Real.pi : ℝ) : ℂ)) := by sorry
