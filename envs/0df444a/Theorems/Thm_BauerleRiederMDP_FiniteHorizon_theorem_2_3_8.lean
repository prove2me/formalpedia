-- Prove2me | Theorems.Thm_BauerleRiederMDP_FiniteHorizon_theorem_2_3_8
-- name    : BauerleRiederMDP.FiniteHorizon.theorem_2_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:28:37.898775+00:00
-- url     : https://prove2.me/theorems/6a6dcac8-2f79-4bd9-bbf1-d01af8ad4506
-- title:
--   Theorem 2.3.8 (Structure Theorem) — the value functions solve the Bellman equation and every sequence of maximizers is optimal
-- statement:
--   Let $(A_N)$ hold and let the Structure Assumption $(SA_N)$ be satisfied by the sets $\mathbb M_n$ and $\Delta_n$. Then:
--
--   1. $V_n\in\mathbb M_n$ for $n=0,\dots,N$, and $(V_n)$ satisfies the Bellman equation: for $x\in E$ and $n=0,\dots,N-1$,
--
--   $$V_N(x)=g_N(x),\qquad V_n(x)=\sup_{a\in D_n(x)}\Big\{r_n(x,a)+\int V_{n+1}(x')\,Q_n(dx'\mid x,a)\Big\};$$
--
--   2. $V_n=T_nT_{n+1}\cdots T_{N-1}g_N$;
--   3. for $n=0,\dots,N-1$ there exist maximizers $f_n$ of $V_{n+1}$ with $f_n\in\Delta_n$, and every sequence of maximizers $f_n^*$ of $V_{n+1}$ defines an optimal policy $(f_0^*,\dots,f_{N-1}^*)$.
--
--   Here $V_n$ is the supremum of the expected total reward over all Markov policies, so the theorem says that backward induction computes the true value. This is the central result of the book's finite-horizon theory: every concrete model is solved by checking $(SA_N)$.
--
--   **Formalization Note.** $V_n$ is defined from the path law, not by the recursion, so 1 and 2 are not definitional. A sequence of maximizers is a `Policy` because a maximizer is a decision rule.
--
--   Differences from the source:
--   - reading: T_n v is well-defined in (SA_N)(ii) → for every (x,a) ∈ D_n the positive and negative parts of v do not both have infinite Q_n-integral (TWellDefined); reason: Definition 2.3.1 defines L_n v "whenever the integral exists"
--   - encoding: Q_n and r_n are defined on D_n → Q_n and r_n are defined on E × A (MDPFinance.Bellman.MarkovDecisionModel); reason: D_n is measurable, so every book model extends (for example by δ_x and 0), and values off D_n enter no statement
--   - encoding: 𝔼^π_{nx} is the expectation under the conditional probability ℙ^π(· | X_n = x) → the expectation under the kernel pathKernel, forward composition of the Q_k, recording states and actions; reason: this is the regular version of the conditional law, defined at every x
--   - encoding: E and A are sets → E and A lie in one universe, as in MDPFinance.Bellman.Hist; reason: a Lean universe convention; no mathematical instance is lost, since a space can be lifted
--   - encoding: integrals of [−∞, ∞)-valued functions → erealIntegral, the EReal difference of the Lebesgue integrals of the two parts, with −∞ when both are infinite; reason: (A_N) and (SA_N)(ii) exclude that case wherever the statement uses an integral
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 2.3.8, p.23

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
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_TChain

open MeasureTheory ProbabilityTheory
open MDPFinance.Bellman (MarkovDecisionModel IsMaximizer erealIntegral)

namespace BauerleRiederMDP.FiniteHorizon

universe u

/-- Theorem 2.3.8 (Structure Theorem) (Bäuerle & Rieder, Markov Decision Processes with
Applications to Finance (2011), p.23, PDF 38). Let (SA_N) be satisfied, under the standing
assumption (A_N). Then
a) `V_n ∈ IM_n`, `V_N = g_N` and `V_n(x) = sup_{a ∈ D_n(x)} {r_n(x, a) + ∫ V_{n+1}(x') Q_n(dx'|x, a)}`;
b) `V_n = T_n T_{n+1} … T_{N-1} g_N`;
c) for `n = 0, …, N-1` there exist maximizers `f_n` of `V_{n+1}` with `f_n ∈ Δ_n`, and every
sequence of maximizers `f*_n` of `V_{n+1}` defines an optimal policy.

**Formalization Note.** `V` is the supremum over policies of expectations under the path law, so
a) and b) are not definitional. A sequence of maximizers is a `Policy`, since a maximizer is a
decision rule. -/
theorem theorem_2_3_8 {E A : Type u} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (hAN : IntegrabilityAssumption M)
    (IMs : ℕ → Set (E → EReal)) (Deltas : ℕ → Set (E → A))
    (hSAN : StructureAssumption M IMs Deltas) :
    (∀ n ≤ N, V M n ∈ IMs n) ∧
    (∀ x, V M N x = (M.g x : EReal)) ∧
    (∀ n < N, ∀ x, V M n x =
      ⨆ a ∈ M.Dx n x, ((M.r n (x, a) : EReal) + erealIntegral (M.Q n (x, a)) (V M (n + 1)))) ∧
    (∀ n ≤ N, V M n = TChain M (N - n) n (fun x => (M.g x : EReal))) ∧
    (∀ n < N, ∃ f ∈ Deltas n, IsMaximizer M n (V M (n + 1)) f) ∧
    (∀ π : Policy M, (∀ n : Fin N, IsMaximizer M n (V M (n + 1)) (π.1 n)) → IsOptimal M π) := by sorry

end BauerleRiederMDP.FiniteHorizon
