-- Prove2me | Theorems.Thm_BranchRepairs_small_range_margin
-- name    : BranchRepairs.small_range_margin
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T03:28:58.015428+00:00
-- url     : https://prove2.me/theorems/e234c1aa-da56-4110-b275-44bbd6841689
-- title:
--   small range margin — BranchRepairs
-- statement:
--   Vale a desigualdade racional exata
--   $$ 9\cdot24\left(\frac1{10000^2}+\frac1{10000^3}\right)<\frac12. $$
--   Ela certifica apenas a margem numérica indicada.
--
--   Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Inventário documental V3, PF28 FINAL 15/11/2026. BranchRepairs.small_range_margin; fonte BRANCH_REPAIRS.lean; SHA256 original 044e027c4764608082de3e11b57a2ce18282197670adc8726daa23be725e17f7. Sem reivindicação de novidade.

import Mathlib
open Filter Topology

theorem BranchRepairs.small_range_margin :
    (9*24 : ℝ) * (1/(10000:ℝ)^2 + 1/(10000:ℝ)^3) < 1/2 := by sorry
