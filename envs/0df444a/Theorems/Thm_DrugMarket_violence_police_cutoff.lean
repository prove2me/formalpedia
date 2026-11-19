-- Prove2me | Theorems.Thm_DrugMarket_violence_police_cutoff
-- name    : DrugMarket.violence_police_cutoff
-- status  : Proved
-- author  : @LG
-- created : 2026-11-16T13:38:30.031043+00:00
-- url     : https://prove2.me/theorems/4ef7b3e0-6699-4ef1-9d5e-e1be10552708
-- title:
--   Police-violence cutoff for retail violence
-- statement:
--   $dv^*/dv_r=(1+\ln\hat q)/\ln q$. Since $\ln q<0$, retail violence increases with police violence iff $\ln\hat q<-1$, decreases iff $\ln\hat q>-1$, and is stationary iff $\ln\hat q=-1$.
-- source:
--   Gilberto José Nogueira Júnior, *Mercado de Drogas e Repressão: Efeitos da Intervenção Governamental sobre a Violência gerada pelo Mercado de Drogas numa Rede Verticalmente Relacionada*, MSc dissertation, UFPE/PIMES, 2019, Chapter 3. Eq. (3.39), Appendix (A.3)–(A.4).

import Mathlib
import Definitions.Def_drug_market_model
import Definitions.Def_drug_market_equilibrium

namespace DrugMarket
theorem violence_police_cutoff (q s v_r g : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1) (hs : 0 < s) (hvr : 0 < v_r) (hg : 0 ≤ g) :
  deriv (fun vr => violenceBR q s vr g) v_r = (1 + Real.log (qHat q s v_r g)) / Real.log q ∧ (deriv (fun vr => violenceBR q s vr g) v_r > 0 ↔ Real.log (qHat q s v_r g) < -1) ∧ (deriv (fun vr => violenceBR q s vr g) v_r < 0 ↔ -1 < Real.log (qHat q s v_r g)) ∧ (deriv (fun vr => violenceBR q s vr g) v_r = 0 ↔ Real.log (qHat q s v_r g) = -1) := by sorry
end DrugMarket
