-- Prove2me | Theorems.Thm_BranchRepairs_bernoulli_inverse_bound
-- name    : BranchRepairs.bernoulli_inverse_bound
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T03:27:12.115812+00:00
-- url     : https://prove2.me/theorems/e2bac6e0-42aa-4fb6-8d11-dd2afdff45d6
-- title:
--   bernoulli inverse bound — BranchRepairs
-- statement:
--   Cota inversa de Bernoulli para expoente natural, d ≥ 0 e z > 0.
--   Escopo limitado às hipóteses formais. Não constitui prova de RH nem valida os ramos analíticos.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Inventário documental V3, PF28 FINAL 15/11/2026. BranchRepairs.bernoulli_inverse_bound; fonte BRANCH_REPAIRS.lean; SHA256 original 044e027c4764608082de3e11b57a2ce18282197670adc8726daa23be725e17f7. Sem reivindicação de novidade.

import Mathlib
open Filter Topology

theorem BranchRepairs.bernoulli_inverse_bound (m : ℕ) (d z : ℝ)
    (hd : 0 ≤ d) (hz : 0 < z) :
    ((1 + d/z)^m)⁻¹ ≤ (1 + (m:ℝ)*d/z)⁻¹ := by sorry
