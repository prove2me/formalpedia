-- Prove2me | Theorems.Thm_FoodTrace_Adoption_lemma_5
-- name    : FoodTrace.Adoption.lemma_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:45:34.641081+00:00
-- url     : https://prove2.me/theorems/bee0c372-4068-492a-bcd7-03d6470ea4b0
-- title:
--   Lemma 5 — BPC implies r^e_N < r^e_T and (1 − ρ_e)^n > 1 − ρ
-- statement:
--   Under the standing assumptions, suppose the Break Point Criterion holds:
--   $$\pi^e_{0T}(r^e_T) < \pi^e_{0N}(r^e_T),$$
--   where $\pi^e_{0T}(r) = n(1-\rho_e)(r - w^e_T)$ and $\pi^e_{0N}(r) = n(1-\rho_e)^n(r - w^e_N)$. Then
--
--   1. the effort threshold without traceability is below the one with traceability, $r^e_N < r^e_T$;
--   2. $(1-\rho_e)^n > 1-\rho$: the survival probability of the whole chain without traceability when every farm exerts effort exceeds a single farm's survival probability without effort.
--
--   These two facts are the necessary conditions of BPC used in the proof of Proposition 3.
-- source:
--   Dong, Jiang & Xu, Impact of Traceability Technology Adoption in Food Supply Chain Networks, Management Science (accepted manuscript, SSRN 3484664, March 2022), p. 21, Lemma 5

import Mathlib
import Definitions.Def_FoodTrace_Adoption_Model

namespace FoodTrace.Adoption

/-- Lemma 5 (p. 21): if BPC holds, then `r^e_N < r^e_T` and `(1 − ρ_e)^n > 1 − ρ`. -/
theorem lemma_5 (P : Params) (hP : Standing P) (hBPC : BPC P) :
    rNe P < rTe P ∧ 1 - P.ρ < (1 - P.ρe) ^ P.n := by sorry

end FoodTrace.Adoption
