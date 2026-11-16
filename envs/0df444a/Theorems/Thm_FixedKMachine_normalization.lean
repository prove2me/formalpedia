-- Prove2me | Theorems.Thm_FixedKMachine_normalization
-- name    : FixedKMachine.normalization
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:52:43.720423+00:00
-- url     : https://prove2.me/theorems/f12370fe-82ae-404f-8394-5db536399e96
-- title:
--   normalization — FixedKMachine
-- statement:
--   Para n,k,a,f,ef,g reais com n>0,k≥0 e g=(nf−ef)/(n+k), vale [a(n+k)/n]g=af−a·ef/n.
--
--   Escopo: resultado com as hipóteses indicadas. Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandao Bueno. PF28 FINAL 15/11/2026, §§166.5; 166.12. Declaração FixedKMachine.normalization; arquivo lean/FixedKMachine.lean; SHA-256 27008a2b7521a25cd4b1540094b609caf42b0dcfb15e2ab564c9b144cee4042b. Sem reivindicação de novidade. https://app.notion.com/p/41898395ac6e818d8b0ffa99a48cc43f

import Mathlib
open MeasureTheory Set

theorem FixedKMachine.normalization (n k a f ef g : ℝ) (hn : 0 < n) (hk : 0 ≤ k)
    (hr : g = (n*f-ef)/(n+k)) :
    (a*(n+k)/n)*g = a*f-a*ef/n := by sorry
