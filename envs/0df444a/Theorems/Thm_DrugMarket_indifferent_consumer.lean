-- Prove2me | Theorems.Thm_DrugMarket_indifferent_consumer
-- name    : DrugMarket.indifferent_consumer
-- status  : Proved
-- author  : @Lucas
-- created : 2026-11-16T13:35:37.894079+00:00
-- url     : https://prove2.me/theorems/24acc90e-1987-4a90-b407-0e9033e1ce53
-- title:
--   Indifferent consumer and Hotelling demand
-- statement:
--   With outlets at the endpoints ($a=0$, $1-b=1$) and $t>0$, a consumer located at $x\in[0,1]$ is indifferent between the two outlets exactly when $x=\tfrac12+(p_b-p_a)/(2t)$. The violence disutility $z(v_a+v_b+v_r)$ is common to both outlets and cancels, so the location choice reacts to prices only, not to violence.
-- source:
--   Gilberto José Nogueira Júnior, *Mercado de Drogas e Repressão: Efeitos da Intervenção Governamental sobre a Violência gerada pelo Mercado de Drogas numa Rede Verticalmente Relacionada*, MSc dissertation, UFPE/PIMES, 2019, Chapter 3. Eq. (3.5)–(3.7).

import Mathlib
import Definitions.Def_drug_market_model
import Definitions.Def_drug_market_equilibrium

namespace DrugMarket
theorem indifferent_consumer (u z t p_a p_b v_a v_b v_r x : ℝ) (ht : 0 < t) (hx : x ∈ Set.Icc (0:ℝ) 1) :
  utilA u z t p_a v_a v_b v_r x = utilB u z t p_b v_a v_b v_r x ↔ x = (1:ℝ)/2 + (p_b - p_a)/(2*t) := by sorry
end DrugMarket
