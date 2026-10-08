-- Prove2me | Theorems.Thm_AssortSearch_Cannibal_T_increasing
-- name    : AssortSearch.Cannibal.T_increasing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:31:47.672155+00:00
-- url     : https://prove2.me/theorems/48928e91-ff52-4f0c-8bbb-8f6463ad67d4
-- title:
--   $T(\omega)=\omega(1-e^{-\lambda/\omega})$ has $T'(\omega)=1-(1+\lambda/\omega)e^{-\lambda/\omega}$ and is strictly increasing on $(0,\infty)$
-- statement:
--   Let $\lambda>0$ and $T(\omega)=\omega\big(1-\exp(-\lambda/\omega)\big)$ for $\omega>0$. Then for every $\omega>0$
--   $$
--   T'(\omega)=1-\Big(1+\frac{\lambda}{\omega}\Big)\exp\Big(-\frac{\lambda}{\omega}\Big),
--   $$
--   and $T$ is strictly increasing on $(0,\infty)$. This is the auxiliary function of the proof of Theorem 2: the demand $q_i^{si}(S)$ is $v_i$ times $T$ evaluated at the reciprocal of $\sum_{k\in S}v_k+v_0$.
--
--   **Formalization Note** The paper writes "increasing on the interval $[0,\infty)$", where $T(0)$ is undefined; the statement is on the open interval $(0,\infty)$, and "increasing" is read as strictly increasing, which is what Theorem 2's strict inequality needs.
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 10 (PDF 12), proof of Theorem 2

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model
import Definitions.Def_AssortSearch_Cannibal_Model

open MeasureTheory ProbabilityTheory

namespace AssortSearch.Cannibal

/-- Proof of Theorem 2, p. 10: for a positive constant `λ`, `T(ω) = ω(1 - exp(-λ/ω))` has
derivative `T'(ω) = 1 - (1 + λ/ω) exp(-λ/ω)` and is strictly increasing on `(0, ∞)`. -/
theorem T_increasing (lam : ℝ) (hlam : 0 < lam) :
    (∀ ω : ℝ, 0 < ω →
      HasDerivAt (T lam) (1 - (1 + lam / ω) * Real.exp (-lam / ω)) ω) ∧
    StrictMonoOn (T lam) (Set.Ioi 0) := by sorry

end AssortSearch.Cannibal
