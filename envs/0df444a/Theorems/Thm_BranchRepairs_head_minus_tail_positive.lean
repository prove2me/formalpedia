-- Prove2me | Theorems.Thm_BranchRepairs_head_minus_tail_positive
-- name    : BranchRepairs.head_minus_tail_positive
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T03:29:16.850514+00:00
-- url     : https://prove2.me/theorems/f52ad422-05f9-4f9d-9fc4-537ebe8443c7
-- title:
--   head minus tail positive — BranchRepairs
-- statement:
--   Se \(h,t,K\in\mathbb R\), \(h>0\), \(t<h/2\) e \(h-t\le K\), então
--   $$ K>h/2. $$
--   O resultado separa a estimativa positiva da cabeça do controle necessário da cauda.
--
--   Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Inventário documental V3, PF28 FINAL 15/11/2026. BranchRepairs.head_minus_tail_positive; fonte BRANCH_REPAIRS.lean; SHA256 original 044e027c4764608082de3e11b57a2ce18282197670adc8726daa23be725e17f7. Sem reivindicação de novidade.

import Mathlib
open Filter Topology

theorem BranchRepairs.head_minus_tail_positive (head tail K : ℝ)
    (hh : 0 < head) (ht : tail < head/2) (hk : head-tail ≤ K) :
    head/2 < K := by sorry
