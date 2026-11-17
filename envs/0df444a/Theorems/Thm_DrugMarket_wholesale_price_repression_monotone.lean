-- Prove2me | Theorems.Thm_DrugMarket_wholesale_price_repression_monotone
-- name    : DrugMarket.wholesale_price_repression_monotone
-- status  : Proved
-- author  : @Lucas
-- created : 2026-11-16T13:41:06.850825+00:00
-- url     : https://prove2.me/theorems/bfbd4185-09fb-490c-b047-dd16ce9e605f
-- title:
--   Repression raises wholesale prices
-- statement:
--   $dw_i^*/dv_{ri}>0$: intensifying repression against a wholesaler raises its equilibrium wholesale price, passing the expected repression cost downstream.
-- source:
--   Gilberto José Nogueira Júnior, *Mercado de Drogas e Repressão: Efeitos da Intervenção Governamental sobre a Violência gerada pelo Mercado de Drogas numa Rede Verticalmente Relacionada*, MSc dissertation, UFPE/PIMES, 2019, Chapter 3. Eq. (3.52).

import Mathlib
import Definitions.Def_drug_market_model
import Definitions.Def_drug_market_equilibrium

namespace DrugMarket
theorem wholesale_price_repression_monotone (q s t c v_ra v_rb : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1) (hs : 0 < s) (ht : 0 < t) (hvra : 0 < v_ra) (hvrb : 0 < v_rb) :
  deriv (fun vra => wholesalePriceA q s t c vra v_rb) v_ra > 0 ∧ deriv (fun vrb => wholesalePriceB q s t c v_ra vrb) v_rb > 0 := by sorry
end DrugMarket
