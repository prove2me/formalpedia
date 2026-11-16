-- Prove2me | Theorems.Thm_FixedKMachine_branch_machine
-- name    : FixedKMachine.branch_machine
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:59:45.275966+00:00
-- url     : https://prove2.me/theorems/36b5af0c-50c8-479c-bc8d-8750442f7653
-- title:
--   Lema condicional: branch machine — FixedKMachine
-- statement:
--   Sejam H,F,I,N proposições. Suponha ¬H⇒F∨I, H⇒¬N, N⇒¬F e N⇒¬I. Então ¬N. As exclusões dos dois casos são hipóteses deste lema lógico; o enunciado não demonstra os Branches 2 e 3 da função zeta.
--
--   Escopo: resultado com as hipóteses indicadas. Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandao Bueno. PF28 FINAL 15/11/2026, §§166.5; 166.12. Declaração FixedKMachine.branch_machine; arquivo lean/FixedKMachine.lean; SHA-256 27008a2b7521a25cd4b1540094b609caf42b0dcfb15e2ab564c9b144cee4042b. Sem reivindicação de novidade. https://app.notion.com/p/41898395ac6e818d8b0ffa99a48cc43f

import Mathlib
open MeasureTheory Set

theorem FixedKMachine.branch_machine (H F I N : Prop)
    (hcases : ¬H → F ∨ I) (hRH : H → ¬N)
    (hfinite : N → ¬F) (hinfinite : N → ¬I) : ¬N := by sorry
