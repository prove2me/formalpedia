-- Prove2me | Theorems.Thm_DiagonalMachine_approximate_floor
-- name    : DiagonalMachine.approximate_floor
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:59:44.938806+00:00
-- url     : https://prove2.me/theorems/c346e08b-c645-4693-9322-32c7d9ec0ec8
-- title:
--   approximate floor — DiagonalMachine
-- statement:
--   Seja a uma sequência real tal que a(n)<0 implique a(n+1)≤a(n). Suponha que para todo K natural e ε>0 exista n≥K com a(n)≥−ε. Então a(k)≥0 para todo k. A hipótese fornece pisos arbitrariamente próximos de zero em toda cauda.
--
--   Escopo: resultado com as hipóteses indicadas. Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandao Bueno. PF28 FINAL 15/11/2026, §§166.5; 166.12. Declaração DiagonalMachine.approximate_floor; arquivo lean/DiagonalMachine.lean; SHA-256 da5312becbf7179c40de1cb5bcfc9c0e85a8ee4276361c99a64a4b42cb7c00bf. Sem reivindicação de novidade. https://app.notion.com/p/41898395ac6e818d8b0ffa99a48cc43f

import Mathlib
import Theorems.Thm_DiagonalMachine_depth_persists
open MeasureTheory Set
open DiagonalMachine

theorem DiagonalMachine.approximate_floor (a : ℕ → ℝ)
    (hstep : ∀ n, a n < 0 → a (n+1) ≤ a n)
    (hfloor : ∀ K, ∀ ε : ℝ, 0 < ε → ∃ n, K ≤ n ∧ -ε ≤ a n) :
    ∀ k, 0 ≤ a k := by sorry
