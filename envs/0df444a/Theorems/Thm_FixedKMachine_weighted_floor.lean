-- Prove2me | Theorems.Thm_FixedKMachine_weighted_floor
-- name    : FixedKMachine.weighted_floor
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:59:35.966409+00:00
-- url     : https://prove2.me/theorems/145c84d8-05e9-4347-bdad-4dcb2d703ea1
-- title:
--   weighted floor — FixedKMachine
-- statement:
--   Seja s um conjunto finito de naturais e w,g funções reais. Se w(i)≥0, g(i)≥m para i∈s e Σ_{i∈s}w(i)=1, então Σ_{i∈s}w(i)g(i)≥m.
--
--   Escopo: resultado com as hipóteses indicadas. Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandao Bueno. PF28 FINAL 15/11/2026, §§166.5; 166.12. Declaração FixedKMachine.weighted_floor; arquivo lean/FixedKMachine.lean; SHA-256 27008a2b7521a25cd4b1540094b609caf42b0dcfb15e2ab564c9b144cee4042b. Sem reivindicação de novidade. https://app.notion.com/p/41898395ac6e818d8b0ffa99a48cc43f

import Mathlib
open MeasureTheory Set

theorem FixedKMachine.weighted_floor (w g : ℕ → ℝ) (s : Finset ℕ) (m : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hfloor : ∀ i ∈ s, m ≤ g i)
    (hsum : ∑ i ∈ s, w i = 1) : m ≤ ∑ i ∈ s, w i*g i := by sorry
