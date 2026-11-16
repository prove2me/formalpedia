-- Prove2me | Theorems.Thm_ExternalTowerTest_base_nonnegative
-- name    : ExternalTowerTest.base_nonnegative
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T03:32:04.090341+00:00
-- url     : https://prove2.me/theorems/c89b21d9-9281-41db-af25-39346c89a7c7
-- title:
--   base nonnegative — ExternalTowerTest
-- statement:
--   Defina \(u_k=(1+2^k)/2\) e \(v_k=(1-2^k)/2\). No andar inicial,
--   $$ u_0\ge0\quad\text{e}\quad v_0\ge0. $$
--   Esta é uma afirmação sobre o modelo explícito, não sobre a torre dos zeros.
--
--   Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Inventário documental V3, PF28 FINAL 15/11/2026. ExternalTowerTest.base_nonnegative; fonte TowerControl.lean; SHA256 original 8149db870743309507796830831d1a8e5d77b5979e5cdf7df299e56c8017fadb. Sem reivindicação de novidade.

import Mathlib
open Filter Topology

theorem ExternalTowerTest.base_nonnegative : 0 ≤ ((1 + (2 : ℝ)^0)/2) ∧ 0 ≤ ((1 - (2 : ℝ)^0)/2) := by sorry
