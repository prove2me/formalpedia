-- Prove2me | Theorems.Thm_ExternalTowerTest_stable_negative
-- name    : ExternalTowerTest.stable_negative
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T03:33:23.520693+00:00
-- url     : https://prove2.me/theorems/f86d5b27-a3e1-4ae7-93a6-fd815f39e886
-- title:
--   stable negative — ExternalTowerTest
-- statement:
--   Sejam \(v,w,e,d\in\mathbb R\). Se \(v\le-d\), \(|w-v|\le e\) e \(e<d\), então
--   $$ w<0. $$
--   O lema exprime a preservação de uma margem negativa sob uma perturbação controlada.
--
--   Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Inventário documental V3, PF28 FINAL 15/11/2026. ExternalTowerTest.stable_negative; fonte TowerControl.lean; SHA256 original 8149db870743309507796830831d1a8e5d77b5979e5cdf7df299e56c8017fadb. Sem reivindicação de novidade.

import Mathlib
open Filter Topology

theorem ExternalTowerTest.stable_negative (v w e d : ℝ)
    (hv : v ≤ -d) (herr : |w-v| ≤ e) (he : e < d) : w < 0 := by sorry
