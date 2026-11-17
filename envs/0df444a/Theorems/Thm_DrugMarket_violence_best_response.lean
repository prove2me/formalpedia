-- Prove2me | Theorems.Thm_DrugMarket_violence_best_response
-- name    : DrugMarket.violence_best_response
-- status  : Proved
-- author  : @Lucas
-- created : 2026-11-16T13:37:55.304623+00:00
-- url     : https://prove2.me/theorems/ff3189c2-d9fa-4280-a547-d426c588b05a
-- title:
--   Retail violence best response and corner solution
-- statement:
--   The retailer's violence objective $(1-q^{v/v_r})\pi'-s\,q^{v/v_r}-v$ is strictly concave on $[0,\infty)$. With $\hat q=-v_r/(\ln q\,(\pi'+s))$, if $\hat q<1$ its unique maximizer is $v^*=v_r\ln\hat q/\ln q>0$; if $\hat q\ge1$ the unique maximizer is the corner $v=0$.
-- source:
--   Gilberto José Nogueira Júnior, *Mercado de Drogas e Repressão: Efeitos da Intervenção Governamental sobre a Violência gerada pelo Mercado de Drogas numa Rede Verticalmente Relacionada*, MSc dissertation, UFPE/PIMES, 2019, Chapter 3. Eq. (3.26)–(3.35) and the corner discussion.

import Mathlib
import Definitions.Def_drug_market_model
import Definitions.Def_drug_market_equilibrium

namespace DrugMarket
theorem violence_best_response (q s v_r g : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1) (hs : 0 < s) (hvr : 0 < v_r) (hg : 0 ≤ g) :
  (qHat q s v_r g < 1 → ∀ v ∈ Set.Ici (0:ℝ), retailViolenceObjective q s v_r g v ≤ retailViolenceObjective q s v_r g (violenceBR q s v_r g) ∧ (retailViolenceObjective q s v_r g v = retailViolenceObjective q s v_r g (violenceBR q s v_r g) ↔ v = violenceBR q s v_r g)) ∧ (1 ≤ qHat q s v_r g → ∀ v ∈ Set.Ici (0:ℝ), retailViolenceObjective q s v_r g v ≤ retailViolenceObjective q s v_r g 0 ∧ (retailViolenceObjective q s v_r g v = retailViolenceObjective q s v_r g 0 ↔ v = 0)) := by sorry
end DrugMarket
