-- Prove2me | Theorems.Thm_BauerleRiederMDP_LQ_Supplement_theorem_8_3_2
-- name    : BauerleRiederMDP.LQ.Supplement.theorem_8_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:02:15.892111+00:00
-- url     : https://prove2.me/theorems/c542d5e1-3e18-4313-9ec3-3e95db7cbed3
-- title:
--   Theorem 8.3.2 — the finite-horizon chain and its embedded infinite-stage model have the same values
-- statement:
--   For a Markov policy $\pi  = (f_n)$ we have $V_\pi (t, x) = J_{\infty (f_n)}(t, x)$, $(t, x) \in  E' = [0, T] \times  E$. Moreover, $V = J_\infty $.
--
--   **Formalization Note.** The chain is the published `PDMDP.FiniteChain` (countable $E$), with $V_\pi $ and $V$ the published `FiniteChain.Vpi` and `FiniteChain.V` (from the path law, a supremum over Markov policies), under the Integrability Assumption (A) of p.258. The embedded model (8.13)–(8.14) is `finiteChainEmbStage` and $J_\infty $ is `finiteChainEmbJinf`. Both assertions are stated for every $t \in  [0, T]$, including $t = T$, where both sides are $g(x)$.
--
--   Differences from the source:
--   - encoding: cemetery state Δ → substochastic StageModel, cemetery skipped; reason: as the book does; same values
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 8.3.2, p.259 (PDF 270)

import Mathlib
import Definitions.Def_BauerleRiederMDP_PDMDP_DecisionRule
import Definitions.Def_BauerleRiederMDP_PDMDP_RateModel
import Definitions.Def_BauerleRiederMDP_PDMDP_StageModel
import Definitions.Def_BauerleRiederMDP_PDMDP_FiniteChain
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_finiteChainEmbStage
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_finiteChainEmbJinf
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_finiteChainIntegrabilityA

open BauerleRiederMDP.PDMDP

namespace BauerleRiederMDP.LQ.Supplement

/-- **Theorem 8.3.2** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance*
(2011), Theorem 8.3.2, p.259, PDF 270, finite-horizon chain of pp.258–259, PDF 269–270). For a
Markov policy `π = (f_n)` we have `V_π(t, x) = J_{∞(f_n)}(t, x)`, `(t, x) ∈ E′ = [0, T] × E`.
Moreover, `V = J_∞`.

**Formalization Note.** The chain is the published `PDMDP.FiniteChain` (countable `E`), with
`V_π` and `V` the published `FiniteChain.Vpi` and `FiniteChain.V` (from the path law, a supremum
over Markov policies), under the Integrability Assumption (A) of p.258. The embedded model
(8.13)–(8.14) is `finiteChainEmbStage` and `J_∞` is `finiteChainEmbJinf`. Both assertions are stated for every
`t ∈ [0, T]`, including `t = T`, where both sides are `g(x)`. -/
theorem theorem_8_3_2 {E U : Type*} [MeasurableSpace E] [Countable E]
    [MeasurableSingletonClass E] [MeasurableSpace U] (C : FiniteChain E U)
    (hA : finiteChainIntegrabilityA C) :
    (∀ (π : ℕ → DecisionRule (ℝ × E) U) (t : ℝ), t ∈ Set.Icc 0 C.horizon → ∀ x : E,
      C.Vpi π t x = (finiteChainEmbStage C).Jinf (fun n => (π n).control) (t, x)) ∧
    ∀ t : ℝ, t ∈ Set.Icc 0 C.horizon → ∀ x : E, C.V t x = finiteChainEmbJinf C (t, x) := by sorry

end BauerleRiederMDP.LQ.Supplement
