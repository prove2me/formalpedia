-- Prove2me | Theorems.Thm_ExternalTowerTest_refute_positive_average
-- name    : ExternalTowerTest.refute_positive_average
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T03:33:33.137285+00:00
-- url     : https://prove2.me/theorems/eb5e4c51-cddc-4b21-b38f-c28566edf3b1
-- title:
--   refute positive average — ExternalTowerTest
-- statement:
--   É falsa a afirmação de que, para todos \(a,b\in\mathbb R\), as condições
--   $$ a+b=1,\qquad \tfrac34a+\tfrac14b\ge0,\qquad \tfrac14a+\tfrac34b\ge0 $$
--   implicam \(a\ge0\) e \(b\ge0\). Assim, a positividade dessas duas médias não certifica a positividade de cada componente.
--
--   Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Inventário documental V3, PF28 FINAL 15/11/2026. ExternalTowerTest.refute_positive_average; fonte TowerControl.lean; SHA256 original 8149db870743309507796830831d1a8e5d77b5979e5cdf7df299e56c8017fadb. Sem reivindicação de novidade.

import Mathlib
open Filter Topology

theorem ExternalTowerTest.refute_positive_average :
    ¬ (∀ a b : ℝ, a+b=1 →
      0 ≤ (3/4:ℝ)*a+(1/4:ℝ)*b →
      0 ≤ (1/4:ℝ)*a+(3/4:ℝ)*b → 0 ≤ a ∧ 0 ≤ b) := by sorry
