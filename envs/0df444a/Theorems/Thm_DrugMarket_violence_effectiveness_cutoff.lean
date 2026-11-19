-- Prove2me | Theorems.Thm_DrugMarket_violence_effectiveness_cutoff
-- name    : DrugMarket.violence_effectiveness_cutoff
-- status  : Proved
-- author  : @LG
-- created : 2026-11-16T13:39:09.569564+00:00
-- url     : https://prove2.me/theorems/a3ee9565-0407-4a9c-a474-dbf55e41ec33
-- title:
--   Repression-effectiveness cutoff for retail violence
-- statement:
--   $dv^*/dq=-v_r(1+\ln\hat q)/(q\ln^2 q)$. Retail violence increases with repression effectiveness $q$ iff $\ln\hat q<-1$, decreases iff $\ln\hat q>-1$, and is stationary iff $\ln\hat q=-1$.
-- source:
--   Gilberto José Nogueira Júnior, *Mercado de Drogas e Repressão: Efeitos da Intervenção Governamental sobre a Violência gerada pelo Mercado de Drogas numa Rede Verticalmente Relacionada*, MSc dissertation, UFPE/PIMES, 2019, Chapter 3. Eq. (3.36), Appendix (A.1)–(A.2).

import Mathlib
import Definitions.Def_drug_market_model
import Definitions.Def_drug_market_equilibrium

namespace DrugMarket
theorem violence_effectiveness_cutoff (q s v_r g : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1) (hs : 0 < s) (hvr : 0 < v_r) (hg : 0 ≤ g) :
  deriv (fun qq => violenceBR qq s v_r g) q = -(v_r * (1 + Real.log (qHat q s v_r g))) / (q * (Real.log q)^2) ∧ (deriv (fun qq => violenceBR qq s v_r g) q > 0 ↔ Real.log (qHat q s v_r g) < -1) ∧ (deriv (fun qq => violenceBR qq s v_r g) q < 0 ↔ -1 < Real.log (qHat q s v_r g)) ∧ (deriv (fun qq => violenceBR qq s v_r g) q = 0 ↔ Real.log (qHat q s v_r g) = -1) := by sorry
end DrugMarket
