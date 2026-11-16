-- Prove2me | Theorems.Thm_BranchRepairs_summable_majorant
-- name    : BranchRepairs.summable_majorant
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T03:28:42.681436+00:00
-- url     : https://prove2.me/theorems/a5b811d2-5a0b-40d3-a561-17b3569efde0
-- title:
--   summable majorant — BranchRepairs
-- statement:
--   Sejam \(m\in\mathbb N\), \(m>0\), \(d\ge0\) e \(0<z\le2m\). Então
--   $$ (1+d/z)^{-m}\le(1+d/2)^{-1}. $$
--   Esta cota pontual pode servir na construção de um majorante; não estabelece, sozinha, a somabilidade de uma família de termos.
--
--   Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Inventário documental V3, PF28 FINAL 15/11/2026. BranchRepairs.summable_majorant; fonte BRANCH_REPAIRS.lean; SHA256 original 044e027c4764608082de3e11b57a2ce18282197670adc8726daa23be725e17f7. Sem reivindicação de novidade.

import Mathlib
open Filter Topology

theorem BranchRepairs.summable_majorant (m : ℕ) (d z : ℝ)
    (hm : 0 < m) (hd : 0 ≤ d) (hz : 0 < z) (hzm : z ≤ 2*(m:ℝ)) :
    ((1 + d/z)^m)⁻¹ ≤ (1 + d/2)⁻¹ := by sorry
