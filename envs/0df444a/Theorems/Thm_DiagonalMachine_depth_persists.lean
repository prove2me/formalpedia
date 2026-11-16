-- Prove2me | Theorems.Thm_DiagonalMachine_depth_persists
-- name    : DiagonalMachine.depth_persists
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:52:26.351956+00:00
-- url     : https://prove2.me/theorems/2f899fd3-ad32-4018-8e12-a119b5260011
-- title:
--   depth persists — DiagonalMachine
-- statement:
--   Seja a uma sequência real tal que a(n)<0 implique a(n+1)≤a(n). Se a(k)<0, então a(k+j)≤a(k) para todo j natural. O resultado trata de valores de uma sequência; nenhuma testemunha analítica de mínimo é construída.
--
--   Escopo: resultado com as hipóteses indicadas. Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandao Bueno. PF28 FINAL 15/11/2026, §§166.5; 166.12. Declaração DiagonalMachine.depth_persists; arquivo lean/DiagonalMachine.lean; SHA-256 da5312becbf7179c40de1cb5bcfc9c0e85a8ee4276361c99a64a4b42cb7c00bf. Sem reivindicação de novidade. https://app.notion.com/p/41898395ac6e818d8b0ffa99a48cc43f

import Mathlib
open MeasureTheory Set

theorem DiagonalMachine.depth_persists (a : ℕ → ℝ)
    (hstep : ∀ n, a n < 0 → a (n+1) ≤ a n)
    (k : ℕ) (hk : a k < 0) : ∀ j, a (k+j) ≤ a k := by sorry
