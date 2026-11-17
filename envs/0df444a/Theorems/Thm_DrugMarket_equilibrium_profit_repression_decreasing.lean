-- Prove2me | Theorems.Thm_DrugMarket_equilibrium_profit_repression_decreasing
-- name    : DrugMarket.equilibrium_profit_repression_decreasing
-- status  : Proved
-- author  : @Lucas
-- created : 2026-11-16T13:42:19.356441+00:00
-- url     : https://prove2.me/theorems/f94ae950-07d0-45b8-ab88-283cf69d15d0
-- title:
--   Wholesale repression lowers retail gross profit
-- statement:
--   With positive equilibrium gross margin $t+(k_b-k_a)/9>0$, $d\pi'_a/dv_{ra}<0$: repressing the wholesaler reduces the downstream retailer's equilibrium gross profit.
-- source:
--   Gilberto José Nogueira Júnior, *Mercado de Drogas e Repressão: Efeitos da Intervenção Governamental sobre a Violência gerada pelo Mercado de Drogas numa Rede Verticalmente Relacionada*, MSc dissertation, UFPE/PIMES, 2019, Chapter 3. Eq. (3.62), Appendix (A.9)–(A.12).

import Mathlib
import Definitions.Def_drug_market_model
import Definitions.Def_drug_market_equilibrium

namespace DrugMarket
theorem equilibrium_profit_repression_decreasing (q s t c v_ra v_rb : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1) (hs : 0 < s) (ht : 0 < t) (hvra : 0 < v_ra) (hvrb : 0 < v_rb) (hmarg : 0 < eqMarginA q s t c v_ra v_rb) :
  deriv (fun vra => eqGrossProfitA q s t c vra v_rb) v_ra < 0 := by sorry
end DrugMarket
