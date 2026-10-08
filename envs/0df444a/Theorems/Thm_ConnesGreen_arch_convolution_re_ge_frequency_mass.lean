-- Prove2me | Theorems.Thm_ConnesGreen_arch_convolution_re_ge_frequency_mass
-- name    : ConnesGreen.arch_convolution_re_ge_frequency_mass
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T03:35:32.606008+00:00
-- url     : https://prove2.me/theorems/988e2ead-4f17-4562-b996-038dc2cd51e7
-- title:
--   Original archimedean lower bound with explicit low-frequency loss
-- statement:
--   For B,T>=0 and an unchanged original admissible test g supported in (-T,T), the original archimedean convolution term is at least [gammaBracket(B)-(gammaBracket(B)-gammaBracket(0))*(2 B T/pi)] times the global squared-norm mass of g. This is exactly the existing native theorem with its original gamma definition unfolded in the public signature. Genuine weighted convergence, the exact archimedean identity, gamma order bounds, full Mellin mass and the accepted original low-frequency fraction bound justify every integral comparison. Original convolution/involution and test closure are retained. No endpoint inequality, Weil positivity, surrogate zero set or RH premise is introduced.
-- source:
--   monocap-tech/weil at 6365e9fa26ba7faf91910d5a8270cb3f2cc34551; ArchimedeanEnergy.lean. Original native declarations unchanged. Exact native definition normalization checks accompany both ports.

import Definitions.Def_ConnesGreen_canonical_model
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect.ConnesNative Set
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

theorem ConnesGreen.arch_convolution_re_ge_frequency_mass (B T : ℝ) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (g : ℝ → ℂ) (hg : SupportedTest T g) :
    (((Complex.digamma (1/4 + I*B/2)).re - Real.log Real.pi) -
      (((Complex.digamma (1/4 + I*B/2)).re - Real.log Real.pi) - ((Complex.digamma (1/4 : ℂ)).re - Real.log Real.pi)) * (2 * B * T / Real.pi)) *
        (∫ s : ℝ, ‖g s‖ ^ 2) ≤ (archTerm (conv g (starInv g))).re := by sorry
