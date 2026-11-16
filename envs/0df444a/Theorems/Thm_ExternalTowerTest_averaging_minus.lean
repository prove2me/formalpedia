-- Prove2me | Theorems.Thm_ExternalTowerTest_averaging_minus
-- name    : ExternalTowerTest.averaging_minus
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T03:31:54.234696+00:00
-- url     : https://prove2.me/theorems/a87b1efb-c162-4a01-87d2-5ff87fbfe52e
-- title:
--   averaging minus — ExternalTowerTest
-- statement:
--   Para \(k\in\mathbb N\), defina \(u_k=(1+2^k)/2\) e \(v_k=(1-2^k)/2\). Então
--   $$ v_k=\tfrac14u_{k+1}+\tfrac34v_{k+1}. $$
--   Esta recorrência é uma propriedade do modelo de duas componentes.
--
--   Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Inventário documental V3, PF28 FINAL 15/11/2026. ExternalTowerTest.averaging_minus; fonte TowerControl.lean; SHA256 original 8149db870743309507796830831d1a8e5d77b5979e5cdf7df299e56c8017fadb. Sem reivindicação de novidade.

import Mathlib
open Filter Topology

theorem ExternalTowerTest.averaging_minus (k : ℕ) :
    ((1 - (2 : ℝ)^k)/2) = (1/4 : ℝ)*((1 + (2 : ℝ)^(k+1))/2) + (3/4 : ℝ)*((1 - (2 : ℝ)^(k+1))/2) := by sorry
