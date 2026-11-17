-- Prove2me | Theorems.Thm_DrugMarket_repression_success_monotone
-- name    : DrugMarket.repression_success_monotone
-- status  : Proved
-- author  : @Lucas
-- created : 2026-11-16T13:37:14.801187+00:00
-- url     : https://prove2.me/theorems/62a15960-f84f-48de-ad4b-8e5ea3992c3a
-- title:
--   Monotonicity of the repression technology
-- statement:
--   For $q\in(0,1)$ and $v_r,v_i>0$, the police success probability against a retailer, $q^{v_i/v_r}$, is strictly increasing in police violence $v_r$ and strictly decreasing in the dealer's violence $v_i$.
-- source:
--   Gilberto José Nogueira Júnior, *Mercado de Drogas e Repressão: Efeitos da Intervenção Governamental sobre a Violência gerada pelo Mercado de Drogas numa Rede Verticalmente Relacionada*, MSc dissertation, UFPE/PIMES, 2019, Chapter 3. Eq. (3.12).

import Mathlib
import Definitions.Def_drug_market_model
import Definitions.Def_drug_market_equilibrium

namespace DrugMarket
theorem repression_success_monotone (q v_r v_i : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1) (hvr : 0 < v_r) (hvi : 0 < v_i) :
  deriv (fun vr => catchRetail q vr v_i) v_r > 0 ∧ deriv (fun vi => catchRetail q v_r vi) v_i < 0 := by sorry
end DrugMarket
