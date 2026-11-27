-- Prove2me | Theorems.Thm_BauerleRiederMDP_LQ_Supplement_theorem_2_4_10
-- name    : BauerleRiederMDP.LQ.Supplement.theorem_2_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T23:49:06.188939+00:00
-- url     : https://prove2.me/theorems/f7565416-1b2d-472f-bcf2-f52b56835e49
-- title:
--   Theorem 2.4.10 (corrected last sentence) — continuous models satisfy (SA_N); continuous maximizers under uniqueness
-- statement:
--   Suppose a Markov Decision Model with upper bounding function $b$ is given and for all $n = 0, 1, \dots , N - 1$: (i) $D_n(x)$ is compact for all $x \in  E$ and $x \mapsto  D_n(x)$ is continuous, (ii) $(x, a) \mapsto  \int  v(x') Q_n(dx'|x, a)$ is continuous for all continuous $v \in  IB_b^+$, (iii) $(x, a) \mapsto  r_n(x, a)$ is continuous, (iv) $x \mapsto  g_N(x)$ is continuous. Then the sets `IM_n := {v ∈ IB_b^+ | v is continuous}` and $\Delta _n := F_n$ satisfy the Structure Assumption (SA_N). "If the maximizer of $V_n$ is unique, then $\Delta _n$ can be chosen as the set of continuous functions" is stated in the two forms that Proposition 2.4.8 supports: 1. if $V_{n+1}$ has a unique maximizer at time $n$ ($D^*_n(x)$ is a singleton for every $x$), then there is a continuous maximizer of $V_{n+1}$, and every maximizer of $V_{n+1}$ is continuous; 2. if every $v \in  IM_{n+1}$ has a unique maximizer at time $n$, for every $n < N$, then the sets $IM_n$ and `Δ_n := {f ∈ F_n | f continuous}` satisfy (SA_N).
--
--   **Formalization Note.** The last printed sentence, read as "uniqueness for $V_{n+1}$ alone lets $\Delta _n$ be the continuous rules in (SA_N)", is false, since (SA_N)(iii) quantifies over every $v \in  IM_{n+1}$ ($E = A = [-1, 1]$, next state $xa$, $r = -|a|$, $g = 0$, $N = 1$: the maximizer of $V_1 = 0$ is unique, yet $v(y) = 10y$ has no continuous maximizer); the printed index $V_n$ is a slip for $V_{n+1}$. Uniqueness means $D^*_n(x) := \{a \in  D_n(x) | L_n v(x, a) = T_n v(x)\}$ has at most one point for every $x$ (p.33); it is nonempty by (SA_N). $E$, $A$ are Borel spaces with $D_n$ Borel (§2.4, p.29); (ii), (iii) are continuity on $D_n$ with its relative topology; continuity of $x \mapsto  D_n(x)$ is Definition A.2.1 c) (published `ContinuousSetValued`); $IB_b^+$ is the published `IBbPlus`.
--
--   Differences from the source:
--   - correction: if the maximizer of V_n is unique, Δ_n can be chosen as the set of continuous functions → (1) uniqueness for V_{n+1} gives a continuous maximizer and every maximizer is continuous; (2) uniqueness for every v ∈ IM_{n+1} lets Δ_n be the continuous rules in (SA_N); reason: false as printed: E = A = [−1,1], next state xa, r = −|a|, g = 0, N = 1; the maximizer of V_1 = 0 is unique, yet v(y) = 10y has no continuous maximizer; V_n is a slip for V_{n+1}
--   - encoding: E, A Borel spaces → metrizable second-countable standard Borel encoding; reason: Lean encoding; same instances
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 2.4.10, p.33 (PDF 48)

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
open MDPFinance.Bellman (MarkovDecisionModel IsDecisionRule IsMaximizer erealIntegral L T)
open MDPFinance.Contracting (IBbPlus ContinuousSetValued)
open BauerleRiederMDP.FiniteHorizon

namespace BauerleRiederMDP.LQ.Supplement

universe u

/-- **Theorem 2.4.10** (corrected last sentence) (Bäuerle & Rieder, *Markov Decision Processes
with Applications to Finance* (2011), Theorem 2.4.10, p.33, PDF 48). Suppose a Markov Decision
Model with upper bounding function `b` is given and for all `n = 0, 1, …, N − 1`:
(i) `D_n(x)` is compact for all `x ∈ E` and `x ↦ D_n(x)` is continuous,
(ii) `(x, a) ↦ ∫ v(x′) Q_n(dx′|x, a)` is continuous for all continuous `v ∈ IB_b^+`,
(iii) `(x, a) ↦ r_n(x, a)` is continuous,
(iv) `x ↦ g_N(x)` is continuous.
Then the sets `IM_n := {v ∈ IB_b^+ | v is continuous}` and `Δ_n := F_n` satisfy the Structure
Assumption (SA_N). "If the maximizer of `V_n` is unique, then `Δ_n` can be chosen as the set of
continuous functions" is stated in the two forms that Proposition 2.4.8 supports:
1. if `V_{n+1}` has a unique maximizer at time `n` (`D*_n(x)` is a singleton for every `x`), then
there is a continuous maximizer of `V_{n+1}`, and every maximizer of `V_{n+1}` is continuous;
2. if every `v ∈ IM_{n+1}` has a unique maximizer at time `n`, for every `n < N`, then the sets
`IM_n` and `Δ_n := {f ∈ F_n | f continuous}` satisfy (SA_N).

**Formalization Note.** The last printed sentence, read as "uniqueness for `V_{n+1}` alone lets
`Δ_n` be the continuous rules in (SA_N)", is false, since (SA_N)(iii) quantifies over every
`v ∈ IM_{n+1}` (`E = A = [−1, 1]`, next state `xa`, `r = −|a|`, `g = 0`, `N = 1`: the maximizer of
`V_1 = 0` is unique, yet `v(y) = 10y` has no continuous maximizer); the printed index `V_n` is a
slip for `V_{n+1}`. Uniqueness means `D*_n(x) := {a ∈ D_n(x) | L_n v(x, a) = T_n v(x)}` has at most
one point for every `x` (p.33); it is nonempty by (SA_N). `E`, `A` are Borel spaces with `D_n`
Borel (§2.4, p.29); (ii), (iii) are continuity on `D_n` with its relative topology; continuity of
`x ↦ D_n(x)` is Definition A.2.1 c) (published `ContinuousSetValued`); `IB_b^+` is the published
`IBbPlus`. -/
theorem theorem_2_4_10 {E A : Type u}
    [TopologicalSpace E] [TopologicalSpace.MetrizableSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E] [StandardBorelSpace E]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (b : E → ℝ) (hb : IsUpperBoundingFunction M b)
    (hD_cpt : ∀ n < N, ∀ x, IsCompact (M.Dx n x))
    (hD_cont : ∀ n < N, ContinuousSetValued (M.Dx n))
    (hQ : ∀ n < N, ∀ v ∈ IBbPlus b, Continuous v →
      ContinuousOn (fun xa => erealIntegral (M.Q n xa) v) (M.D n))
    (hr : ∀ n < N, ContinuousOn (M.r n) (M.D n))
    (hg : Continuous M.g) :
    StructureAssumption M (fun _ => {v | v ∈ IBbPlus b ∧ Continuous v})
        (fun n => {f | IsDecisionRule M n f}) ∧
      (∀ n < N,
        (∀ x, {a | a ∈ M.Dx n x ∧ L M n (V M (n + 1)) (x, a) = T M n (V M (n + 1)) x}.Subsingleton) →
        (∃ f, IsMaximizer M n (V M (n + 1)) f ∧ Continuous f) ∧
          ∀ f, IsMaximizer M n (V M (n + 1)) f → Continuous f) ∧
      ((∀ n < N, ∀ v ∈ {v | v ∈ IBbPlus b ∧ Continuous v}, ∀ x,
          {a | a ∈ M.Dx n x ∧ L M n v (x, a) = T M n v x}.Subsingleton) →
        StructureAssumption M (fun _ => {v | v ∈ IBbPlus b ∧ Continuous v})
          (fun n => {f | IsDecisionRule M n f ∧ Continuous f})) := by sorry

end BauerleRiederMDP.LQ.Supplement
