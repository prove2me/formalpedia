-- Prove2me | Theorems.Thm_BauerleRiederMDP_LQ_Supplement_theorem_8_2_1
-- name    : BauerleRiederMDP.LQ.Supplement.theorem_8_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:00:31.97655+00:00
-- url     : https://prove2.me/theorems/5fc99bea-388d-45c0-b09c-6fc996cbeab6
-- title:
--   Theorem 8.2.1 — the piecewise deterministic model and its embedded discrete-time model have the same values
-- statement:
--   For a Markov policy $\pi  = (f_n)$ we have $V_\pi (x) = J_{\infty (f_n)}(x)$, $x \in  E$. Moreover, $V_\infty  = J_\infty $.
--
--   **Formalization Note.** The Piecewise Deterministic Markov Decision Model is the published `PDMDP.Model` (Definition 8.1.1, $E$ a Borel subset of $\mathbb R ^d$, discount rate $\beta  \ge  0$, so $\beta  = 0$ is allowed), under the Integrability Assumption (A) of p.245. $V_\pi $ and $V_\infty $ are the published $Vpi$ (computed from the law of the continuous-time process) and `Vinf` (a supremum over Markov policies). The embedded model $(E, A, D, Q', r')$ of (8.4)–(8.5) is the published `stage`, a substochastic model with the cemetery skipped; $J_{\infty (f_n)}$ is its `Jinf` along the controls $f_n(Z'_n)$ and $J_\infty $ the published `JumpModel.Jinf`, a supremum over all Markov policies $(f_n)$. The control action space $U$ is any measurable space.
--
--   Differences from the source:
--   - generalization: U a Borel space → U any measurable space; reason: the identity uses no topology on U; Borel spaces are a special case
--   - encoding: J_{∞(f_n)} = 𝔼 ∑ r′(Z′_n, f_n(Z′_n)) → the published StageModel.Jinf (limit of the n-stage values); reason: under (A) the partial sums converge; same values
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 8.2.1, p.248 (PDF 259)

import Mathlib
import Definitions.Def_BauerleRiederMDP_PDMDP_Model
import Definitions.Def_BauerleRiederMDP_PDMDP_DecisionRule
import Definitions.Def_BauerleRiederMDP_PDMDP_JumpModel
import Definitions.Def_BauerleRiederMDP_PDMDP_JumpModel_Vinf
import Definitions.Def_BauerleRiederMDP_PDMDP_StageModel
import Definitions.Def_BauerleRiederMDP_PDMDP_JumpModel_relaxedStage
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_PDIntegrabilityA

open MeasureTheory ProbabilityTheory
open BauerleRiederMDP.PDMDP

namespace BauerleRiederMDP.LQ.Supplement

/-- **Theorem 8.2.1** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance*
(2011), Theorem 8.2.1, p.248, PDF 259, embedded model (8.4)–(8.5), p.247, PDF 258). For a Markov
policy `π = (f_n)` we have `V_π(x) = J_{∞(f_n)}(x)`, `x ∈ E`. Moreover, `V_∞ = J_∞`.

**Formalization Note.** The Piecewise Deterministic Markov Decision Model is the published
`PDMDP.Model` (Definition 8.1.1, `E` a Borel subset of `ℝ^d`, discount rate `β ≥ 0`, so `β = 0` is
allowed), under the Integrability Assumption (A) of p.245. `V_π` and `V_∞` are the published
`Vpi` (computed from the law of the continuous-time process) and `Vinf` (a supremum over Markov
policies). The embedded model `(E, A, D, Q′, r′)` of (8.4)–(8.5) is the published `stage`, a
substochastic model with the cemetery skipped; `J_{∞(f_n)}` is its `Jinf` along the controls
`f_n(Z′_n)` and `J_∞` the published `JumpModel.Jinf`, a supremum over all Markov policies `(f_n)`.
The control action space `U` is any measurable space. -/
theorem theorem_8_2_1 {d : ℕ} {E : Set (EuclideanSpace ℝ (Fin d))} {U : Type*}
    [MeasurableSpace U] (M : Model E U) (hA : PDIntegrabilityA M.toJumpModel) :
    (∀ (π : ℕ → DecisionRule E U) (x : E),
      M.Vpi π x = M.stage.Jinf (fun n => (π n).control) x) ∧
    M.Vinf = M.Jinf := by sorry

end BauerleRiederMDP.LQ.Supplement
