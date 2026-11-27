-- Prove2me | Theorems.Thm_BauerleRiederMDP_LQ_Supplement_theorem_2_4_6
-- name    : BauerleRiederMDP.LQ.Supplement.theorem_2_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T23:48:33.315125+00:00
-- url     : https://prove2.me/theorems/7a1b7cc9-89b6-4760-ac89-979012c1e165
-- title:
--   Theorem 2.4.6 — semicontinuous models satisfy (SA_N); values are usc, maximizers exist and give an optimal policy
-- statement:
--   Suppose the Markov Decision Model has an upper bounding function $b$ and for all $n = 0, 1, \dots , N - 1$: (i) $D_n(x)$ is compact for all $x \in  E$ and $x \mapsto  D_n(x)$ is upper semicontinuous, (ii) $(x, a) \mapsto  \int  v(x') Q_n(dx'|x, a)$ is upper semicontinuous for all upper semicontinuous $v \in  IB_b^+$, (iii) $(x, a) \mapsto  r_n(x, a)$ is upper semicontinuous, (iv) $x \mapsto  g_N(x)$ is upper semicontinuous. Then the sets `IM_n := {v ∈ IB_b^+ | v is upper semicontinuous}` and $\Delta _n := F_n$ satisfy the Structure Assumption (SA_N). In particular, $V_n \in  IM_n$ and there exists a maximizer $f^*_n \in  F_n$ of $V_{n+1}$. The policy $(f^*_0, \dots , f^*_{N-1})$ is optimal.
--
--   **Formalization Note.** $E$, $A$ are Borel spaces and $D_n$ is Borel (§2.4, p.29), encoded as in the published Theorem A.2.3. (ii) and (iii) are upper semicontinuity on $D_n$ with its relative topology, where $Q_n$ and $r_n$ are defined. Upper semicontinuity of $x \mapsto  D_n(x)$ is Definition A.2.1 a) (the published sequential `USCSetValued`). $IB_b^+$ is the published `MDPFinance.Contracting.IBbPlus` ($v \in  IM(E)$, $v^+ \le  c b$, p.29), and the integral of a $[-\infty , \infty )$-valued $v$ is `erealIntegral`. (A_N) follows from the bounding function (Proposition 2.4.2) and is not assumed. $V_n$ is the supremum over policies of the path-law value. "The policy $(f^*_0, \dots , f^*_{N-1})$ is optimal" is stated for every policy formed by maximizers of $V_{n+1}$, together with the existence of such maximizers.
--
--   Differences from the source:
--   - encoding: E, A Borel spaces, D_n Borel → metrizable second-countable standard Borel encoding as in the published Theorem A.2.3; reason: Lean encoding of Borel spaces; same instances
--   - reading: "the policy (f*_0, …, f*_{N−1}) is optimal" → existence of maximizers and optimality of every policy formed by maximizers of V_{n+1}; reason: the book refers to the maximizers just shown to exist; every such choice is optimal
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 2.4.6, p.31 (PDF 46)

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_MDPFinance_Bellman_History
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_Policy
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_stepKernel
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_pathKernel
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_pathReward
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_markovRule
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_Vpi
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_V
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_deltaN
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_IntegrabilityAssumption
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_IsOptimal
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_TWellDefined
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_StructureAssumption
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_IsUpperBoundingFunction
import Definitions.Def_MDPFinance_Contracting_Model
import Definitions.Def_MDPFinance_Contracting_Bounding
import Definitions.Def_MDPFinance_Contracting_LsSet

open MeasureTheory ProbabilityTheory
open MDPFinance.Bellman (MarkovDecisionModel IsDecisionRule IsMaximizer erealIntegral)
open MDPFinance.Contracting (IBbPlus USCSetValued)
open BauerleRiederMDP.FiniteHorizon

namespace BauerleRiederMDP.LQ.Supplement

universe u

/-- **Theorem 2.4.6** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance*
(2011), Theorem 2.4.6, p.31, PDF 46). Suppose the Markov Decision Model has an upper bounding
function `b` and for all `n = 0, 1, …, N − 1`:
(i) `D_n(x)` is compact for all `x ∈ E` and `x ↦ D_n(x)` is upper semicontinuous,
(ii) `(x, a) ↦ ∫ v(x′) Q_n(dx′|x, a)` is upper semicontinuous for all upper semicontinuous
`v ∈ IB_b^+`,
(iii) `(x, a) ↦ r_n(x, a)` is upper semicontinuous,
(iv) `x ↦ g_N(x)` is upper semicontinuous.
Then the sets `IM_n := {v ∈ IB_b^+ | v is upper semicontinuous}` and `Δ_n := F_n` satisfy the
Structure Assumption (SA_N). In particular, `V_n ∈ IM_n` and there exists a maximizer
`f*_n ∈ F_n` of `V_{n+1}`. The policy `(f*_0, …, f*_{N−1})` is optimal.

**Formalization Note.** `E`, `A` are Borel spaces and `D_n` is Borel (§2.4, p.29), encoded as in the
published Theorem A.2.3. (ii) and (iii) are upper semicontinuity on `D_n` with its relative
topology, where `Q_n` and `r_n` are defined. Upper semicontinuity of `x ↦ D_n(x)` is Definition
A.2.1 a) (the published sequential `USCSetValued`). `IB_b^+` is the published
`MDPFinance.Contracting.IBbPlus` (`v ∈ IM(E)`, `v⁺ ≤ c b`, p.29), and the integral of a
`[−∞, ∞)`-valued `v` is `erealIntegral`. (A_N) follows from the bounding function (Proposition
2.4.2) and is not assumed. `V_n` is the supremum over policies of the path-law value. "The policy
`(f*_0, …, f*_{N−1})` is optimal" is stated for every policy formed by maximizers of `V_{n+1}`,
together with the existence of such maximizers. -/
theorem theorem_2_4_6 {E A : Type u}
    [TopologicalSpace E] [TopologicalSpace.MetrizableSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E] [StandardBorelSpace E]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (b : E → ℝ) (hb : IsUpperBoundingFunction M b)
    (hD_cpt : ∀ n < N, ∀ x, IsCompact (M.Dx n x))
    (hD_usc : ∀ n < N, USCSetValued (M.Dx n))
    (hQ : ∀ n < N, ∀ v ∈ IBbPlus b, UpperSemicontinuous v →
      UpperSemicontinuousOn (fun xa => erealIntegral (M.Q n xa) v) (M.D n))
    (hr : ∀ n < N, UpperSemicontinuousOn (M.r n) (M.D n))
    (hg : UpperSemicontinuous M.g) :
    StructureAssumption M (fun _ => {v | v ∈ IBbPlus b ∧ UpperSemicontinuous v})
        (fun n => {f | IsDecisionRule M n f}) ∧
      (∀ n ≤ N, V M n ∈ IBbPlus b ∧ UpperSemicontinuous (V M n)) ∧
      (∀ n < N, ∃ f, IsMaximizer M n (V M (n + 1)) f) ∧
      (∀ π : Policy M, (∀ n : Fin N, IsMaximizer M n (V M (n + 1)) (π.1 n)) →
        IsOptimal M π) := by sorry

end BauerleRiederMDP.LQ.Supplement
