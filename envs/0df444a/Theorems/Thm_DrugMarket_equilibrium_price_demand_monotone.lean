-- Prove2me | Theorems.Thm_DrugMarket_equilibrium_price_demand_monotone
-- name    : DrugMarket.equilibrium_price_demand_monotone
-- status  : Proved
-- author  : @Lucas
-- created : 2026-11-16T13:41:44.815201+00:00
-- url     : https://prove2.me/theorems/a7c53152-afc5-4c4a-8dcd-4e8964ff30cf
-- title:
--   Retail price and demand under wholesale repression
-- statement:
--   $dp_a/dv_{ra}>0$ and $dp_a/dv_{rb}>0$; the effect on retailer $a$ of repressing its own supplier exceeds the effect on retailer $b$ ($dp_a/dv_{ra}>dp_b/dv_{ra}$); and the directly linked retailer's demand falls, $dD_a/dv_{ra}<0$.
-- source:
--   Gilberto José Nogueira Júnior, *Mercado de Drogas e Repressão: Efeitos da Intervenção Governamental sobre a Violência gerada pelo Mercado de Drogas numa Rede Verticalmente Relacionada*, MSc dissertation, UFPE/PIMES, 2019, Chapter 3. Eq. (3.63)–(3.64), Appendix (A.5)–(A.8).

import Mathlib
import Definitions.Def_drug_market_model
import Definitions.Def_drug_market_equilibrium

namespace DrugMarket
theorem equilibrium_price_demand_monotone (q s t c v_ra v_rb : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1) (hs : 0 < s) (ht : 0 < t) (hvra : 0 < v_ra) (hvrb : 0 < v_rb) :
  deriv (fun vra => eqRetailPriceA q s t c vra v_rb) v_ra > 0 ∧ deriv (fun vrb => eqRetailPriceA q s t c v_ra vrb) v_rb > 0 ∧ deriv (fun vra => eqRetailPriceA q s t c vra v_rb) v_ra > deriv (fun vra => eqRetailPriceB q s t c vra v_rb) v_ra ∧ deriv (fun vra => eqDemandA q s t c vra v_rb) v_ra < 0 := by sorry
end DrugMarket
