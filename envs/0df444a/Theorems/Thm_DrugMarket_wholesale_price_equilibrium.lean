-- Prove2me | Theorems.Thm_DrugMarket_wholesale_price_equilibrium
-- name    : DrugMarket.wholesale_price_equilibrium
-- status  : Proved
-- author  : @LG
-- created : 2026-11-16T13:40:15.131189+00:00
-- url     : https://prove2.me/theorems/48db0682-3e5e-4644-850d-9c629ce85007
-- title:
--   Wholesale price equilibrium
-- statement:
--   The wholesale first-order conditions hold if and only if $w_a^*=3t+c+(2k_a+k_b)/3$ and $w_b^*=3t+c+(2k_b+k_a)/3$, where $k_i=s\rho_i/(1-\rho_i)$ and $\rho_i=q^{1/v_{ri}}$. (The printed constant $3s$ in (3.50)–(3.51) is corrected to $s/3$, as obtained by solving (3.48)–(3.49).)
-- source:
--   Gilberto José Nogueira Júnior, *Mercado de Drogas e Repressão: Efeitos da Intervenção Governamental sobre a Violência gerada pelo Mercado de Drogas numa Rede Verticalmente Relacionada*, MSc dissertation, UFPE/PIMES, 2019, Chapter 3. Eq. (3.46)–(3.51), constant corrected.

import Mathlib
import Definitions.Def_drug_market_model
import Definitions.Def_drug_market_equilibrium

namespace DrugMarket
theorem wholesale_price_equilibrium (q s t c v_ra v_rb w_a w_b : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1) (hs : 0 < s) (ht : 0 < t) (hvra : 0 < v_ra) (hvrb : 0 < v_rb) :
  (deriv (fun wa => wholesaleProfitA q s t c v_ra wa w_b) w_a = 0 ∧ deriv (fun wb => wholesaleProfitB q s t c v_rb w_a wb) w_b = 0) ↔ (w_a = wholesalePriceA q s t c v_ra v_rb ∧ w_b = wholesalePriceB q s t c v_ra v_rb) := by sorry
end DrugMarket
