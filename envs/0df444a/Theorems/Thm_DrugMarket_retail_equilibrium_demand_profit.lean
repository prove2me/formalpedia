-- Prove2me | Theorems.Thm_DrugMarket_retail_equilibrium_demand_profit
-- name    : DrugMarket.retail_equilibrium_demand_profit
-- status  : Proved
-- author  : @LG
-- created : 2026-11-16T13:36:51.2982+00:00
-- url     : https://prove2.me/theorems/7a245eff-3d13-480f-bd57-97ce7c0041ca
-- title:
--   Equilibrium retail demand and gross profit
-- statement:
--   At the retail price equilibrium, demands are $D_a=\tfrac12+(w_b-w_a)/(6t)$ and $D_b=\tfrac12+(w_a-w_b)/(6t)$, and gross profits are $\pi'_a=(t+(w_b-w_a)/3)^2/(2t)$ and $\pi'_b=(t+(w_a-w_b)/3)^2/(2t)$.
-- source:
--   Gilberto José Nogueira Júnior, *Mercado de Drogas e Repressão: Efeitos da Intervenção Governamental sobre a Violência gerada pelo Mercado de Drogas numa Rede Verticalmente Relacionada*, MSc dissertation, UFPE/PIMES, 2019, Chapter 3. Eq. (3.23)–(3.25).

import Mathlib
import Definitions.Def_drug_market_model
import Definitions.Def_drug_market_equilibrium

namespace DrugMarket
theorem retail_equilibrium_demand_profit (t w_a w_b : ℝ) (ht : 0 < t) :
  demandA t (retailPriceA t w_a w_b) (retailPriceB t w_a w_b) = (1:ℝ)/2 + (w_b - w_a)/(6*t) ∧ demandB t (retailPriceA t w_a w_b) (retailPriceB t w_a w_b) = (1:ℝ)/2 + (w_a - w_b)/(6*t) ∧ (retailPriceA t w_a w_b - w_a) * demandA t (retailPriceA t w_a w_b) (retailPriceB t w_a w_b) = grossProfitA t w_a w_b ∧ (retailPriceB t w_a w_b - w_b) * demandB t (retailPriceA t w_a w_b) (retailPriceB t w_a w_b) = grossProfitB t w_a w_b := by sorry
end DrugMarket
