-- Prove2me | Theorems.Thm_ExternalTowerTest_all_upper_levels_negative
-- name    : ExternalTowerTest.all_upper_levels_negative
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T03:32:13.666944+00:00
-- url     : https://prove2.me/theorems/38274846-9753-47e4-b235-021be3ea3b79
-- title:
--   all upper levels negative — ExternalTowerTest
-- statement:
--   Para \(k\in\mathbb N\) com \(k\ge1\), defina \(v_k=(1-2^k)/2\). Então
--   $$ v_k<0. $$
--   No modelo de duas componentes, a não negatividade da base não implica a não negatividade dos andares superiores.
--
--   Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Inventário documental V3, PF28 FINAL 15/11/2026. ExternalTowerTest.all_upper_levels_negative; fonte TowerControl.lean; SHA256 original 8149db870743309507796830831d1a8e5d77b5979e5cdf7df299e56c8017fadb. Sem reivindicação de novidade.

import Mathlib
open Filter Topology

theorem ExternalTowerTest.all_upper_levels_negative (k : ℕ) (hk : 1 ≤ k) : ((1 - (2 : ℝ)^k)/2) < 0 := by sorry
