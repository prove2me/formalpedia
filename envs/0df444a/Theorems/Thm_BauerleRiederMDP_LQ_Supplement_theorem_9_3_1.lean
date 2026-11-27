-- Prove2me | Theorems.Thm_BauerleRiederMDP_LQ_Supplement_theorem_9_3_1
-- name    : BauerleRiederMDP.LQ.Supplement.theorem_9_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:04:35.638538+00:00
-- url     : https://prove2.me/theorems/6bf61ec5-f803-4f4c-bcac-f6b8fe1fa504
-- title:
--   Theorem 9.3.1 — pure jump market: the continuous-time problem equals the embedded infinite-stage model
-- statement:
--   a) For a Markov portfolio strategy $\pi  = (\pi _t) = (f_n)$ we have $V_\pi (t, x) = J_{\infty (f_n)}(t, x)$, $(t, x) \in  E$. b) It holds: $V = J_\infty $.
--
--   **Formalization Note.** $U : [0, \infty ) \to  \mathbb R _+$ is a utility function (strictly increasing, strictly concave, continuous). $V_\pi $ is computed from the law of the compound Poisson process (`JumpMarket.Vstrat`); $V$ is the supremum over all predictable strategies (`JMStrategy`), $J_\infty $ over Markov policies of the discrete-time model (`JumpMarket.Jinf`). Laws are built for measurable strategies only. Both statements hold on all of $E = [0, T] \times  \mathbb R _+$, including $x = 0$ and $t = T$.
--
--   Differences from the source:
--   - encoding: predictable portfolio strategies → rules f_n(t − T_n; history; T_n, Z_n) jointly measurable, along i.i.d. (S_n, Y_{n+1}); reason: representation of predictable processes used in the proof (Remark 8.1.2); same class
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 9.3.1, p.283 (PDF 293)

import Mathlib
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_IsUtilityFunction
import Definitions.Def_BauerleRiederMDP_PDMDP_ControlFn
import Definitions.Def_BauerleRiederMDP_PDMDP_RelaxedControl
import Definitions.Def_BauerleRiederMDP_PDMDP_DecisionRule
import Definitions.Def_BauerleRiederMDP_PDMDP_StageModel
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_Ufrac
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_flow
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_relaxedStage
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_stage
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_Jinf
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JMStrategy
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_state
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_Vstrat
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_V
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_markovJMStrategy
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_Eset

open BauerleRiederMDP.PDMDP
open BauerleRiederMDP.RegimeSwitching (IsUtilityFunction)

namespace BauerleRiederMDP.LQ.Supplement

/-- **Theorem 9.3.1** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance*
(2011), Theorem 9.3.1, p.283, PDF 293, model of §9.3, pp.280–283, PDF 290–293).
a) For a Markov portfolio strategy `π = (π_t) = (f_n)` we have `V_π(t, x) = J_{∞(f_n)}(t, x)`,
`(t, x) ∈ E`. b) It holds: `V = J_∞`.

**Formalization Note.** `U : [0, ∞) → ℝ_+` is a utility function (strictly increasing, strictly
concave, continuous). `V_π` is computed from the law of the compound Poisson process
(`JumpMarket.Vstrat`); `V` is the supremum over all predictable strategies (`JMStrategy`), `J_∞`
over Markov policies of the discrete-time model (`JumpMarket.Jinf`). Laws are built for measurable
strategies only. Both statements hold on all of `E = [0, T] × ℝ_+`, including `x = 0` and `t = T`. -/
theorem theorem_9_3_1 {d : ℕ} (Mk : JumpMarket d) (U : ℝ → ℝ)
    (hU : IsUtilityFunction U (Set.Ici 0)) (hU0 : ∀ x, 0 ≤ x → 0 ≤ U x) :
    (∀ (f : ℕ → DecisionRule (ℝ × ℝ) (Ufrac d)), ∀ p ∈ Mk.Eset,
      Mk.Vstrat U (markovJMStrategy f) p = (Mk.stage U).Jinf (fun n => (f n).control) p) ∧
    ∀ p ∈ Mk.Eset, Mk.V U p = Mk.Jinf U p := by sorry

end BauerleRiederMDP.LQ.Supplement
