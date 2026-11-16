-- Prove2me | Theorems.Thm_ExternalTowerTest_averaging_plus
-- name    : ExternalTowerTest.averaging_plus
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T03:30:55.764369+00:00
-- url     : https://prove2.me/theorems/8f9d84f7-f558-4849-a018-e400eca1e612
-- title:
--   averaging plus — ExternalTowerTest
-- statement:
--   Para \(k\in\mathbb N\), defina \(u_k=(1+2^k)/2\) e \(v_k=(1-2^k)/2\). Então
--   $$ u_k=\tfrac34u_{k+1}+\tfrac14v_{k+1}. $$
--   Esta recorrência é uma propriedade do modelo de duas componentes.
--
--   Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Inventário documental V3, PF28 FINAL 15/11/2026. ExternalTowerTest.averaging_plus; fonte TowerControl.lean; SHA256 original 8149db870743309507796830831d1a8e5d77b5979e5cdf7df299e56c8017fadb. Sem reivindicação de novidade.

import Mathlib
open Filter Topology

theorem ExternalTowerTest.averaging_plus (k : ℕ) :
    ((1 + (2 : ℝ)^k)/2) = (3/4 : ℝ)*((1 + (2 : ℝ)^(k+1))/2) + (1/4 : ℝ)*((1 - (2 : ℝ)^(k+1))/2) := by sorry
