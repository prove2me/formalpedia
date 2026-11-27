-- Prove2me | Theorems.Thm_BauerleRiederMDP_LQ_Supplement_theorem_2_3_12
-- name    : BauerleRiederMDP.LQ.Supplement.theorem_2_3_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T23:47:37.631547+00:00
-- url     : https://prove2.me/theorems/e9529650-095a-4838-a498-099ec9d7661f
-- title:
--   Theorem 2.3.12 (corrected: finite value V_n(x) > −∞) — Principle of Dynamic Programming
-- statement:
--   Let (SA_N) be satisfied. Then for $n \le  m \le  N$ and every $x \in  E$ **with $V_n(x) > -\infty $**: $V_{n\pi ^*}(x) = V_n(x) \Rightarrow  V_{m\pi ^*} = V_m$ $\mathbb P ^{\pi ^*}_{nx}$-a.s., i.e. if $(f^*_n, \dots , f^*_{N-1})$ is optimal for the time period $[n, N]$ then $(f^*_m, \dots , f^*_{N-1})$ is optimal for $[m, N]$.
--
--   **Formalization Note.** The bold premise corrects the printed statement, which is false when $V_n(x) = -\infty $ (every policy is then optimal at $x$; counterexample: $N = 2$, the first transition draws $y \in  \mathbb N $ with infinite mean, $A = {0, 1}$, $r_0 = g = 0$, $r_1(y, a) = -y - a$; the policy playing $a = 1$ at time 1 attains $V_0 = -\infty $ but misses $V_1$ at every $y$). The book's proof subtracts $\mathbb E [V_m(X_m) - V_{m\pi ^*}(X_m)]$, which needs a finite value. The standing assumption (A_N) (p.17) is a hypothesis. $\mathbb P ^{\pi ^*}_{nx}$ is the law `pathKernel` of the path from $x$ at time $n$ under $\pi ^*$ up to time $m$ ($m - n$ transitions), and $X_m$ is the last state of that path. $V_{m\pi }$ and $V_m$ are the published path-law value and its supremum over Markov policies.
--
--   Differences from the source:
--   - correction: for every x ∈ E → for every x ∈ E with V_n(x) > −∞; reason: false as printed when V_n(x) = −∞: N = 2, a first transition to y ∈ ℕ with infinite mean, A = {0,1}, r_0 = g = 0, r_1(y,a) = −y − a; the policy playing a = 1 at time 1 attains V_0 = −∞ but misses V_1 at every y
--   - encoding: ℙ^{π*}_{nx}-a.s. at X_m → almost surely under the published path law pathKernel from x at time n; reason: Lean convention for the law of the process; same statement
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 2.3.12, p.26 (PDF 41)

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

open MeasureTheory ProbabilityTheory
open MDPFinance.Bellman (MarkovDecisionModel Hist histState)
open BauerleRiederMDP.FiniteHorizon

namespace BauerleRiederMDP.LQ.Supplement

universe u

/-- **Theorem 2.3.12 (Principle of Dynamic Programming)** (corrected) (Bäuerle & Rieder, *Markov
Decision Processes with Applications to Finance* (2011), Theorem 2.3.12, p.26, PDF 41). Let
(SA_N) be satisfied. Then for `n ≤ m ≤ N` and every `x ∈ E` **with `V_n(x) > −∞`**:
`V_{nπ*}(x) = V_n(x) ⇒ V_{mπ*} = V_m` `ℙ^{π*}_{nx}`-a.s., i.e. if `(f*_n, …, f*_{N−1})` is optimal
for the time period `[n, N]` then `(f*_m, …, f*_{N−1})` is optimal for `[m, N]`.

**Formalization Note.** The bold premise corrects the printed statement, which is false when
`V_n(x) = −∞` (every policy is then optimal at `x`; counterexample: `N = 2`, the first transition
draws `y ∈ ℕ` with infinite mean, `A = {0, 1}`, `r_0 = g = 0`, `r_1(y, a) = −y − a`; the policy
playing `a = 1` at time 1 attains `V_0 = −∞` but misses `V_1` at every `y`). The book's proof
subtracts `𝔼[V_m(X_m) − V_{mπ*}(X_m)]`, which needs a finite value. The standing assumption (A_N)
(p.17) is a hypothesis. `ℙ^{π*}_{nx}` is the law `pathKernel` of the path from `x` at time `n`
under `π*` up to time `m` (`m − n` transitions), and `X_m` is the last state of that path. `V_{mπ}`
and `V_m` are the published path-law value and its supremum over Markov policies. -/
theorem theorem_2_3_12 {E A : Type u} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (hAN : IntegrabilityAssumption M)
    (IMs : ℕ → Set (E → EReal)) (Deltas : ℕ → Set (E → A))
    (hSAN : StructureAssumption M IMs Deltas)
    (π : Policy M) (n m : ℕ) (hnm : n ≤ m) (hmN : m ≤ N) (x : E)
    (hfin : V M n x ≠ ⊥) (hopt : Vpi M π n x = V M n x) :
    ∀ᵐ h ∂(pathKernel M n 0 (markovRule π n) (m - n) x),
      Vpi M π m (histState (0 + (m - n)) h) = V M m (histState (0 + (m - n)) h) := by sorry

end BauerleRiederMDP.LQ.Supplement
