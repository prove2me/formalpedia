-- Prove2me | Theorems.Thm_DiagonalMachine_expanding_window_contradiction
-- name    : DiagonalMachine.expanding_window_contradiction
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:52:33.888099+00:00
-- url     : https://prove2.me/theorems/98756c35-7222-4ca4-aef1-982cacbe689e
-- title:
--   expanding window contradiction — DiagonalMachine
-- statement:
--   Sejam H uma proposição, U uma família real e levels uma sequência de naturais. Suponha U(levels(j),y)≥−1 para todo j natural e |y|≤j. Suponha também que ¬H implique a existência de J tal que, para todo j≥J, algum y com |y|≤j tenha U(levels(j),y)<−1. Então H. O certificado e a entrada nas mesmas janelas são hipóteses explícitas.
--
--   Escopo: resultado com as hipóteses indicadas. Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandao Bueno. PF28 FINAL 15/11/2026, §§166.5; 166.12. Declaração DiagonalMachine.expanding_window_contradiction; arquivo lean/DiagonalMachine.lean; SHA-256 da5312becbf7179c40de1cb5bcfc9c0e85a8ee4276361c99a64a4b42cb7c00bf. Sem reivindicação de novidade. https://app.notion.com/p/41898395ac6e818d8b0ffa99a48cc43f

import Mathlib
open MeasureTheory Set

theorem DiagonalMachine.expanding_window_contradiction (H : Prop) (U : ℕ → ℝ → ℝ)
    (levels : ℕ → ℕ)
    (hcertificate : ∀ (j : ℕ) (y : ℝ), |y| ≤ (j:ℝ) → -1 ≤ U (levels j) y)
    (hentry : ¬H → ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      ∃ y, |y| ≤ (j:ℝ) ∧ U (levels j) y < -1) : H := by sorry
