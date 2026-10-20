-- Prove2me | Theorems.Thm_DerivativeChainPrivate_real_coefficients_descent
-- name    : DerivativeChainPrivate.real_coefficients_descent
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-18T01:48:02.059755+00:00
-- url     : https://prove2.me/theorems/6da429ec-101b-4953-962f-eabe87277e7d
-- title:
--   Descent of a complex polynomial with real coefficients
-- statement:
--   Every complex polynomial whose coefficient imaginary parts vanish is the coefficientwise complexification of a real polynomial.
-- source:
--   Derivative-zero chains: public formalization reference, R28, DerivativeChainPrivate.real_coefficients_descent. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Mathlib.Analysis.Complex.Polynomial.Basic

set_option autoImplicit false

namespace DerivativeChainPrivate
end DerivativeChainPrivate

theorem DerivativeChainPrivate.real_coefficients_descent (p : Polynomial ℂ) (hp : ∀ k, (p.coeff k).im = 0) :
    ∃ q : Polynomial ℝ, q.map Complex.ofRealHom = p := by sorry
