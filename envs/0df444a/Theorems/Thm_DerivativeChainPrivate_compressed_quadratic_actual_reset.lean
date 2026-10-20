-- Prove2me | Theorems.Thm_DerivativeChainPrivate_compressed_quadratic_actual_reset
-- name    : DerivativeChainPrivate.compressed_quadratic_actual_reset
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-19T05:05:31.101529+00:00
-- url     : https://prove2.me/theorems/ae398b72-1ba5-4337-a4d1-4eddc04d2e11
-- title:
--   An actual critical root admits a coefficient-controlled reset detour
-- statement:
--   Let p be a complex polynomial of degree at least two and z any root of its actual derivative. Let M,d,n be naturals with M at least three, d at least two, and Md at most n. Assume each actual root w of p satisfies binomial(n,2d) times norm(w) to the power 2d at most binomial(M,2). Then an actual root w of p satisfies norm(z)+norm(w-z)+norm(w)+1 at most three. The coefficient premise is explicit: this theorem does not derive it from a compressed source or construct the whole derivative chain.
-- source:
--   Derivative-zero chains: public formalization reference, R48, DerivativeChainPrivate.compressed_quadratic_actual_reset. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open Polynomial DerivativeChainPrivate
set_option autoImplicit false

theorem DerivativeChainPrivate.compressed_quadratic_actual_reset (p : Polynomial ℂ)
    (hdegree : 2 ≤ p.natDegree) (z : ℂ) (hz : p.derivative.eval z = 0)
    (n M d : ℕ) (hM : 3 ≤ M) (hd : 2 ≤ d) (hn : M * d ≤ n)
    (hcoeff : ∀ w : ℂ, p.eval w = 0 →
      (n.choose (2 * d) : ℝ) * ‖w‖ ^ (2 * d) ≤ M.choose 2) :
    ∃ w : ℂ, p.eval w = 0 ∧ ‖z‖ + ‖w - z‖ + ‖w‖ + 1 ≤ 3 := by sorry
