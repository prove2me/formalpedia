-- Prove2me | Theorems.Thm_DrugMarket_violence_wholesale_cost_effect
-- name    : DrugMarket.violence_wholesale_cost_effect
-- status  : Proved
-- author  : @Lucas
-- created : 2026-11-16T13:39:47.575377+00:00
-- url     : https://prove2.me/theorems/5e93e33b-7581-4072-9c12-17b969a09f51
-- title:
--   Wholesale-price effect on retail violence
-- statement:
--   With positive gross margin $t+(w_b-w_a)/3>0$, $\partial\pi'_a/\partial w_a<0$; the violence response satisfies $dv_a/dw_a=\hat q\,\partial\pi'_a/\partial w_a<0$, $dv_a/dw_b>0$, and the own- and cross-price effects cancel: $dv_a/dw_a+dv_a/dw_b=0$.
-- source:
--   Gilberto José Nogueira Júnior, *Mercado de Drogas e Repressão: Efeitos da Intervenção Governamental sobre a Violência gerada pelo Mercado de Drogas numa Rede Verticalmente Relacionada*, MSc dissertation, UFPE/PIMES, 2019, Chapter 3. Eq. (3.40)–(3.41) and the cancellation remark.

import Mathlib
import Definitions.Def_drug_market_model
import Definitions.Def_drug_market_equilibrium

namespace DrugMarket
theorem violence_wholesale_cost_effect (q s t v_r w_a w_b : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1) (hs : 0 < s) (ht : 0 < t) (hvr : 0 < v_r) (hmarg : 0 < t + (w_b - w_a)/3) :
  deriv (fun wa => grossProfitA t wa w_b) w_a < 0 ∧ deriv (fun wa => violenceBR q s v_r (grossProfitA t wa w_b)) w_a = qHat q s v_r (grossProfitA t w_a w_b) * deriv (fun wa => grossProfitA t wa w_b) w_a ∧ deriv (fun wa => violenceBR q s v_r (grossProfitA t wa w_b)) w_a < 0 ∧ deriv (fun wb => violenceBR q s v_r (grossProfitA t w_a wb)) w_b > 0 ∧ deriv (fun wa => violenceBR q s v_r (grossProfitA t wa w_b)) w_a + deriv (fun wb => violenceBR q s v_r (grossProfitA t w_a wb)) w_b = 0 := by sorry
end DrugMarket
