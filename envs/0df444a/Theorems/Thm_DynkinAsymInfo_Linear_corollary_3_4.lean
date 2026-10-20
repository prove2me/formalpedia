-- Prove2me | Theorems.Thm_DynkinAsymInfo_Linear_corollary_3_4
-- name    : DynkinAsymInfo.Linear.corollary_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:20.759981+00:00
-- url     : https://prove2.me/theorems/71691ccb-21f4-4a50-bda2-45365c55ad00
-- title:
--   Corollary 3.4 — ex-ante payoff splits by type
-- statement:
--   For continuous nonnegative payoffs $0\le f\le g$, an admissible stopping time $\tau$, and type controls $\Gamma^0,\Gamma^1$, the game payoff is the prior-weighted average
--   $$J(\tau,\Gamma)=(1-\pi)J^0(\tau,\Gamma^0)+\pi J^1(\tau,\Gamma^1).$$
--   Here $J^i$ is the expected survival payoff plus the Stieltjes stopping cost under $P^i=P(\cdot\mid\theta=i)$. This split defines the two informed agents' interim objectives.
--
--   **Formalization Note.** The claim is in the §6 GBM instance. The Stieltjes integral includes the jump at zero, and each conditional expectation is a nonnegative extended integral.
-- source:
--   De Angelis, Ekström, Glover, Dynkin Games with Incomplete and Asymmetric Information, arXiv:1810.07674v5, p. 10, Corollary 3.4, (26)–(27); p. 11, (28)

import Mathlib
import Definitions.Def_DynkinAsymInfo_Linear_Game

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DynkinAsymInfo.Linear
set_option autoImplicit false

/-- De Angelis, Ekström, Glover, arXiv:1810.07674v5, p. 10, Corollary 3.4,
(26)–(28), specialised to the GBM of §6. `J0` and `J1` use the conditional
laws and Stieltjes integrals including the jump at zero. -/
theorem corollary_3_4 {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (x pi : ℝ) (hx : 0 < x) (hpi : pi ∈ Set.Ioo 0 1)
    (f g : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi 0)) (hg : ContinuousOn g (Set.Ioi 0))
    (hfg : ∀ y, 0 < y → 0 ≤ f y ∧ f y ≤ g y)
    (tau : Ω → WithTop ℝ≥0) (htau : InT p st x pi tau)
    (G0 G1 : ℝ≥0 → Ω → ℝ)
    (hG0 : InA st (FX p st x pi) G0) (hG1 : InA st (FX p st x pi) G1) :
    J p st x pi f g tau (mixControl st pi G0 G1) =
      ENNReal.ofReal (1 - pi) * J0 p st x pi f g tau G0 +
      ENNReal.ofReal pi * J1 p st x pi f g tau G1 := by sorry

end DynkinAsymInfo.Linear
