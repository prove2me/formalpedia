-- Prove2me | Theorems.Thm_BauerleRiederMDP_Stopping_theorem_10_1_5
-- name    : BauerleRiederMDP.Stopping.theorem_10_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:30:33.631276+00:00
-- url     : https://prove2.me/theorems/84d4e0f4-05a8-4a67-abf9-1b4f8127c44f
-- title:
--   Theorem 10.1.5 — value iteration, the recursion for $d_n$ and the optimal finite-horizon rule
-- statement:
--   Consider a stationary stopping problem with transition kernel $Q^X$, running reward $c$, stopping reward $g$, discount factor $\beta\in(0,1]$ and finite horizon $N$, under Assumption $(B_N)$. Write $J_n(x)=\sup_{\tau\le n}\mathbb E_x[R_\tau]$ and $Tv(x)=\max\{g(x),\,c(x)+\beta\int v(x')Q^X(dx'\mid x)\}$. Then:
--
--   1. $J_0=g$ and $J_n=TJ_{n-1}$ for $n=1,\dots,N$.
--   2. $g\le J_n\le J_{n+1}$ for all $n\in\mathbb N_0$.
--   3. With $d_n(x):=g(x)-c(x)-\beta\int J_{n-1}(x')Q^X(dx'\mid x)$,
--   $$
--   d_{n+1}(x)=d_1(x)-\beta\int d_n^-(x')\,Q^X(dx'\mid x).
--   $$
--   4. With $S_n^*:=\{x\mid J_n(x)=g(x)\}$: $S_0^*=E$, $S_n^*=\{x\mid d_n(x)\ge0\}$ and $S_{n+1}^*\subset S_n^*$. The policy $(f_N^*,\dots,f_1^*)$ with $f_n^*=1_{S_n^*}$ is optimal, and $\tau^*:=\min\{n\in\{0,\dots,N\}\mid X_n\in S_{N-n}^*\}$ is an optimal stopping time.
--
--   This reduces the finite-horizon stationary problem to backward value iteration and shows that the tendency to stop does not decrease as time goes by.
--
--   **Formalization Note** Clause 2 ranges over all $n$, each $J_n$ being its own $n$-stage problem. The other clauses stay in the range $n\le N$ printed in the book.
--
--   Differences from the source:
--   - encoding: c) d_{n+1}(x) = d_1(x) − β∫d_n^-(x′)Q^X(dx′|x) with no proviso → the identity at every x where the right side is not +∞ − (+∞); reason: when ∫g dQ^X(·|x) = −∞ we have d_1(x) = +∞ and ∫d_n^- dQ^X(·|x) may be +∞, so the printed right side has no meaning; the proviso excludes exactly that undefined case
--   - encoding: the policy (f*_N,…,f*_1) is optimal → its stopping time τ_π = policyTime is optimal; reason: p.305 identifies the value of a policy with E_x[R_{τ_π}]; the same instances
--   - encoding: d_n and S*_n defined from J_{n−1} and J_n → P.d and P.stopSet built on the iterate P.J, which clause a) identifies with J_n for n ≤ N; reason: same values under (B_N)
--   - encoding: integrals in [−∞, ∞) and policies as decision rules f : E → {0,1} → erealIntegral = ∫v⁺ − ∫v⁻ in EReal; a stationary rule is its stopping set S; reason: Lean convention; same instances. Under (B) the positive part is finite, so ∞ − ∞ never arises in these expressions
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 10.1.5, p.308

import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_Stationary
import Definitions.Def_BauerleRiederMDP_Stopping_IsOptimalUpTo

open MeasureTheory
open MDPFinance.OptimalStopping

namespace BauerleRiederMDP.Stopping

/-- **Theorem 10.1.5**, Bäuerle & Rieder, Markov Decision Processes with Applications to Finance
(2011), p.308 (PDF 316), under (B_N). With `J_n = sup_{τ ≤ n} 𝔼_x[R_τ]` (`valueUpTo`, p.307):
a) `J_0 = g`, `J_n = T J_{n-1}` for `n = 1,…,N`; hence `J_n` is the iterate `P.J n` for `n ≤ N`.
b) `g ≤ J_n ≤ J_{n+1}` for all `n ∈ ℕ_0`.
c) `d_{n+1}(x) = d_1(x) − β ∫ d_n^-(x') Q^X(dx'|x)`, wherever the right side is not `∞ − ∞`.
d) `S_0^* = E`, `S_n^* = {d_n ≥ 0}`, `S_{n+1}^* ⊂ S_n^*`; the policy `(f_N^*,…,f_1^*)` is optimal
and `τ^* := min{n ∈ {0,…,N} | X_n ∈ S_{N-n}^*}` is an optimal stopping time.

**Formalization Note.** `P.d n` and `P.stopSet n` are built on the iterate `P.J`, which a) identifies
with `J_n` for `n ≤ N`. b) ranges over all `n`, each `J_n` being its own `n`-stage problem. The
policy `(f_N^*,…,f_1^*)` has decision rule `1_{S_{N-k}^*}` at time `k`; by p.305 its value is
`𝔼_x[R_{τ_π}]` with `τ_π = policyTime`. In c), `d_1(x) = +∞` when `∫ g dQ^X(·|x) = -∞`, and then
`∫ d_n^- dQ^X(·|x)` can be `+∞`; the page's right side has no meaning there, so that case is
excluded. -/
theorem theorem_10_1_5 {E : Type*} [MeasurableSpace E] (P : StationaryProblem E) (N : ℕ)
    (Pr : E → Measure (ℕ → E)) (hPr : P.IsPathLaw Pr) (hBN : P.AssumptionBN Pr N) :
    ((∀ x : E, P.valueUpTo Pr 0 x = (P.g x : EReal)) ∧
      (∀ n : ℕ, 1 ≤ n → n ≤ N → ∀ x : E,
        P.valueUpTo Pr n x = P.T (P.valueUpTo Pr (n - 1)) x) ∧
      (∀ n : ℕ, n ≤ N → ∀ x : E, P.valueUpTo Pr n x = P.J n x)) ∧
    (∀ (n : ℕ) (x : E), (P.g x : EReal) ≤ P.valueUpTo Pr n x ∧
      P.valueUpTo Pr n x ≤ P.valueUpTo Pr (n + 1) x) ∧
    (∀ (n : ℕ) (x : E), 1 ≤ n → n + 1 ≤ N →
      ¬ (P.d 1 x = ⊤ ∧ erealIntegral (P.QX x) (fun y => max (-P.d n y) 0) = ⊤) →
      P.d (n + 1) x =
        P.d 1 x - (P.beta : EReal) * erealIntegral (P.QX x) (fun y => max (-P.d n y) 0)) ∧
    (P.stopSet 0 = Set.univ ∧
      (∀ n : ℕ, 1 ≤ n → n ≤ N → P.stopSet n = {x : E | 0 ≤ P.d n x}) ∧
      (∀ n : ℕ, n < N → P.stopSet (n + 1) ⊆ P.stopSet n) ∧
      IsOptimalUpTo P Pr N (policyTime (fun k => P.stopSet (N - k)) N) ∧
      IsOptimalUpTo P Pr N (hitTimeCapped (fun n => P.stopSet (N - n)) N)) := by sorry

end BauerleRiederMDP.Stopping
