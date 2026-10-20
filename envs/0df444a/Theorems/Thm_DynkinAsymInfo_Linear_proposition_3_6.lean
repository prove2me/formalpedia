-- Prove2me | Theorems.Thm_DynkinAsymInfo_Linear_proposition_3_6
-- name    : DynkinAsymInfo.Linear.proposition_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:20.11098+00:00
-- url     : https://prove2.me/theorems/ff9144d5-e423-404b-bf4d-bd425ddb20cd
-- title:
--   Proposition 3.6 — saddle points and agent-form Nash equilibria
-- statement:
--   Let $\tau^*$ be admissible and let $\Gamma^{*,0},\Gamma^{*,1}$ be two admissible type controls. The induced randomised stopping pair is a saddle point of the ex-ante game if and only if each type's interim cost is minimal against every admissible control and the uninformed player's scaled payoff is maximal against every admissible stopping time:
--   $$J^i(\tau^*,\Gamma^{*,i})\le J^i(\tau^*,\Gamma^i)\quad(i=0,1),\qquad \widehat J(\tau,\Gamma^*)\le\widehat J(\tau^*,\Gamma^*).$$
--   The first two inequalities hold for all admissible $\Gamma^i$, and the last for all admissible $\tau$. This equivalence connects the ex-ante and three-agent formulations.
--
--   **Formalization Note.** The paper's $J^i_{x,\phi}$ is the same conditional payoff as $J^i_{x,\pi}$ with $\pi=\phi/(1+\phi)$.
-- source:
--   De Angelis, Ekström, Glover, Dynkin Games with Incomplete and Asymmetric Information, arXiv:1810.07674v5, p. 11, Proposition 3.6, (30)–(32)

import Mathlib
import Definitions.Def_DynkinAsymInfo_Linear_Game

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DynkinAsymInfo.Linear
set_option autoImplicit false

/-- De Angelis, Ekström, Glover, arXiv:1810.07674v5, p. 11, Proposition 3.6.
Saddle points in the ex-ante game are agent-form Nash equilibria (30)–(32).
This is stated in the §6 GBM instance; `pi=phi/(1+phi)`. -/
theorem proposition_3_6 {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (x phi : ℝ) (hx : 0 < x) (hphi : 0 < phi)
    (f g : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi 0)) (hg : ContinuousOn g (Set.Ioi 0))
    (hfg : ∀ y, 0 < y → 0 ≤ f y ∧ f y ≤ g y)
    (taus : Ω → WithTop ℝ≥0) (htau : InT p st x (phi / (1 + phi)) taus)
    (Gs0 Gs1 : ℝ≥0 → Ω → ℝ)
    (hG0 : InA st (FX p st x (phi / (1 + phi))) Gs0)
    (hG1 : InA st (FX p st x (phi / (1 + phi))) Gs1) :
    let pi := phi / (1 + phi)
    IsSaddle p st x pi f g taus (mixControl st pi Gs0 Gs1) ↔
      (∀ G0, InA st (FX p st x pi) G0 →
        J0 p st x pi f g taus Gs0 ≤ J0 p st x pi f g taus G0) ∧
      (∀ G1, InA st (FX p st x pi) G1 →
        J1 p st x pi f g taus Gs1 ≤ J1 p st x pi f g taus G1) ∧
      (∀ tau, InT p st x pi tau →
        Jhat p st x pi f g tau (mixControl st pi Gs0 Gs1) ≤
          Jhat p st x pi f g taus (mixControl st pi Gs0 Gs1)) := by sorry

end DynkinAsymInfo.Linear
