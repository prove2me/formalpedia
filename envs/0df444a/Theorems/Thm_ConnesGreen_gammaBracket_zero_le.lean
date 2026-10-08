-- Prove2me | Theorems.Thm_ConnesGreen_gammaBracket_zero_le
-- name    : ConnesGreen.gammaBracket_zero_le
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T01:01:00.024196+00:00
-- url     : https://prove2.me/theorems/6bcda518-be2a-4517-acca-4652a94a574b
-- title:
--   The original Connes gamma symbol has its global minimum at zero
-- statement:
--   For every real r, gammaBracket(0) <= gammaBracket(r), where the unchanged original symbol is Re digamma(1/4+i r/2)-log(pi). The public statement unfolds precisely this native definition, with the same r/2 scale and subtraction. A native Lean normalization check verifies that this statement is exactly the existing gammaBracket_zero_le result. It follows from the accepted open-strip vertical minimum at a=1/4. No positivity of the minimum or archimedean integral bound is assumed or proved.
-- source:
--   monocap-tech/weil at 5ba603ccaacf5ea1172c6cf087b8c5f33f029bb5; ArchimedeanEnergy.lean. Original native declarations unchanged. Independent Mathlib-only platform proof audit recovers the original HasSum digamma series.

import Mathlib
import Theorems.Thm_ConnesGreen_digamma_re_vertical_minimum
set_option autoImplicit false
open Complex

theorem ConnesGreen.gammaBracket_zero_le (r : ℝ) : (Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi ≤
      (Complex.digamma (1 / 4 + I * r / 2)).re - Real.log Real.pi := by sorry
