-- Prove2me | Theorems.Thm_ExternalTowerTest_conditional_branches
-- name    : ExternalTowerTest.conditional_branches
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T03:33:14.507193+00:00
-- url     : https://prove2.me/theorems/9081ebf3-baef-4eff-8ea7-d350ed11d48b
-- title:
--   conditional branches — ExternalTowerTest
-- statement:
--   Sejam \(N,F,I,H\) proposições. Suponha
--   $$ \neg H\Rightarrow(F\lor I),\qquad N\Rightarrow\neg F,\qquad N\Rightarrow\neg I,\qquad H\Rightarrow\neg N. $$
--   Então \(\neg N\). Este esquema condicional é uma variante de FixedKMachine.branch_machine. Os ramos são hipóteses, e a letra RH no código designa uma proposição abstrata; a aplicação aos zeros da zeta exige prová-los separadamente.
--
--   Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Inventário documental V3, PF28 FINAL 15/11/2026. ExternalTowerTest.conditional_branches; fonte TowerControl.lean; SHA256 original 8149db870743309507796830831d1a8e5d77b5979e5cdf7df299e56c8017fadb. Sem reivindicação de novidade.

import Mathlib
open Filter Topology

theorem ExternalTowerTest.conditional_branches (Negative FiniteOff InfiniteOff RH : Prop)
    (cases : ¬ RH → FiniteOff ∨ InfiniteOff)
    (branch2 : Negative → ¬ FiniteOff)
    (branch3 : Negative → ¬ InfiniteOff)
    (rh_sign : RH → ¬ Negative) : ¬ Negative := by sorry
