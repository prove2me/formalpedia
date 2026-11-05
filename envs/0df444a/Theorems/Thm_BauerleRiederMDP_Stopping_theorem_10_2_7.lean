-- Prove2me | Theorems.Thm_BauerleRiederMDP_Stopping_theorem_10_2_7
-- name    : BauerleRiederMDP.Stopping.theorem_10_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:30:49.609329+00:00
-- url     : https://prove2.me/theorems/f604c143-55dc-4623-b69a-930878dfe72c
-- title:
--   Theorem 10.2.7 — One-Step-Look-Ahead Rule (corrected: optimality of $\tau^*$ needs the limit form of (B))
-- statement:
--   Consider a stationary stopping problem under Assumption (B), with transition kernel $Q^X$, running reward $c$, stopping reward $g$ and discount factor $\beta\in(0,1]$. Let
--
--   $$
--   S_0:=\Big\{x\in E\ \Big|\ g(x)\ge c(x)+\beta\int g(x')\,Q^X(dx'\mid x)\Big\}
--   $$
--
--   be closed, i.e. $Q^X(S_0\mid x)=1$ for all $x\in S_0$. Then:
--
--   1. The decision rule $f^*=1_{S_0}$ is a maximizer of $J_n$ for every $n\in\mathbb N$ and also of $J$.
--   2. Let $\tau^*:=\inf\{n\in\mathbb N_0\mid X_n\in S_0\}$. Then $\tau^*\wedge N$ is optimal for the $N$-stage stopping problem, for every $N$.
--   3. If $\mathbb P_x(\tau^*<\infty)=1$ for all $x\in E$ and the limit form of (B) in Remark 10.2.1 a) holds, then $\tau^*$ is optimal for the unbounded stopping problem.
--
--   The rule compares the reward from stopping immediately with the reward from stopping one step ahead. When the set where stopping now wins is absorbing, this comparison alone solves the problem.
--
--   **Formalization Note** "Closed" means absorbing under $Q^X$, not topologically closed.
--
--   Differences from the source:
--   - correction: b) if P_x(τ* < ∞) = 1 for all x then τ* is optimal for the unbounded problem under (B) as printed → assumes in addition the limit form of (B) printed in Remark 10.2.1 a), lim_n E_x[R_{τ∧n}] = E_x[R_τ] for all τ < ∞; reason: the printed claim is false. Chain on E = ℕ₀ ∪ {s}: from k to k+1 or s with probability 1/2 each, s absorbing, c = 0, β = 1, g(k) = 2^k − 1/2, g(s) = 0. It satisfies (B): g ≥ 0 gives the liminf part by Fatou and sup_τ E_k[g(X_τ)] ≤ 2^k. Yet τ*, the hitting time of s, is a.s. finite with E_x[R_τ*] = 0 while V*(0) ≥ g(0) = 1/2. Remark 10.2.1 a) calls the limit form equivalent to (B), which this chain refutes
--   - encoding: J_n := sup over stopping times τ ≤ n, J := lim_n J_n → the iterate P.J n and P.Jlim = sup_n P.J n; reason: Theorem 10.1.5 a) (a milestone here) identifies the iterate with the supremum under (B_n), and (B) gives every (B_n); same values
--   - encoding: τ < ∞ with P_x(τ < ∞) = 1 for all x → τ with P_x(τ = ⊤) = 0 for the x at hand, inside the platform definitions of (B) and V*; reason: a stopping time finite under P_x is P_x-a.s. equal to one finite under every P_y (set it to 0 on the X_0-event where P_y(τ < ∞) ≠ 1), so the conditions and values agree
--   - encoding: integrals in [−∞, ∞) and policies as decision rules f : E → {0,1} → erealIntegral = ∫v⁺ − ∫v⁻ in EReal; a stationary rule is its stopping set S; reason: Lean convention; same instances. Under (B) the positive part is finite, so ∞ − ∞ never arises in these expressions
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 10.2.7, p.315

import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_Stationary
import Definitions.Def_BauerleRiederMDP_Stopping_lookAheadSet
import Definitions.Def_BauerleRiederMDP_Stopping_IsOptimalUpTo
import Definitions.Def_BauerleRiederMDP_Stopping_AssumptionBLim

open MeasureTheory
open MDPFinance.OptimalStopping

namespace BauerleRiederMDP.Stopping

/-- **Theorem 10.2.7** (corrected), the **One-Step-Look-Ahead Rule**, Bäuerle & Rieder, Markov
Decision Processes with Applications to Finance (2011), p.315 (PDF 323), under (B). Let
`S_0 := {x | g(x) ≥ c(x) + β ∫ g dQ^X(·|x)}` be closed: `Q^X(S_0|x) = 1` for `x ∈ S_0`. Then
a) `f^* = 1_{S_0}` is a maximizer of `J_n`, `n ∈ ℕ`, and of `J`;
b) with `τ^* := inf{n | X_n ∈ S_0}`, `τ^* ∧ N` is optimal for the `N`-stage problem, and if
`ℙ_x(τ^* < ∞) = 1` for all `x` then, under the limit form of (B) (Remark 10.2.1 a)), `τ^*` is
optimal for the unbounded problem.

**Formalization Note.** "Closed" is absorbing, not topological. `J_n` is the iterate `P.J n` and `J`
is `P.Jlim = sup_n P.J n`; Theorem 10.1.5 a) identifies them with the suprema over stopping times.
`ℕ` on the page starts at `1`. The last clause is false under (B) as printed: see the Differences
section of the natural-language statement. -/
theorem theorem_10_2_7 {E : Type*} [MeasurableSpace E] (P : StationaryProblem E)
    (Pr : E → Measure (ℕ → E)) (hPr : P.IsPathLaw Pr) (hB : P.AssumptionB Pr)
    (hclosed : ∀ x ∈ lookAheadSet P, P.QX x (lookAheadSet P) = 1) :
    ((∀ n : ℕ, 1 ≤ n → P.IsMaximizer (lookAheadSet P) (P.J n)) ∧
      P.IsMaximizer (lookAheadSet P) P.Jlim) ∧
    ((∀ N : ℕ, IsOptimalUpTo P Pr N (truncTime (hitTime (lookAheadSet P)) N)) ∧
      (AssumptionBLim P Pr →
        (∀ x : E, Pr x {w | hitTime (lookAheadSet P) w = ⊤} = 0) →
        P.IsOptimal Pr (hitTime (lookAheadSet P)))) := by sorry

end BauerleRiederMDP.Stopping
