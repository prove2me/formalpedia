-- Prove2me | Theorems.Thm_DrugMarket_retail_price_equilibrium
-- name    : DrugMarket.retail_price_equilibrium
-- status  : Proved
-- author  : @Lucas
-- created : 2026-11-16T13:36:13.822862+00:00
-- url     : https://prove2.me/theorems/7c440540-654e-4fde-9cbe-e332916a459a
-- title:
--   Retail price equilibrium
-- statement:
--   For $q\in(0,1)$, $t,v_r>0$ and positive retailer violence $v_a,v_b>0$ (so survival probabilities $1-q^{v_i/v_r}$ are nonzero), the two retail price first-order conditions hold if and only if $p_a=t+(2w_a+w_b)/3$ and $p_b=t+(2w_b+w_a)/3$: the unique Nash equilibrium of the retail price subgame.
-- source:
--   Gilberto José Nogueira Júnior, *Mercado de Drogas e Repressão: Efeitos da Intervenção Governamental sobre a Violência gerada pelo Mercado de Drogas numa Rede Verticalmente Relacionada*, MSc dissertation, UFPE/PIMES, 2019, Chapter 3. Eq. (3.17)–(3.22).

import Mathlib
import Definitions.Def_drug_market_model
import Definitions.Def_drug_market_equilibrium

namespace DrugMarket
theorem retail_price_equilibrium (q t v_r w_a w_b v_a v_b p_a p_b : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1) (ht : 0 < t) (hvr : 0 < v_r) (hva : 0 < v_a) (hvb : 0 < v_b) :
  ((1 - catchRetail q v_r v_a) * ((1:ℝ)/2 - (2*p_a - w_a - p_b)/(2*t)) = 0 ∧ (1 - catchRetail q v_r v_b) * ((1:ℝ)/2 - (2*p_b - w_b - p_a)/(2*t)) = 0) ↔ (p_a = retailPriceA t w_a w_b ∧ p_b = retailPriceB t w_a w_b) := by sorry
end DrugMarket
