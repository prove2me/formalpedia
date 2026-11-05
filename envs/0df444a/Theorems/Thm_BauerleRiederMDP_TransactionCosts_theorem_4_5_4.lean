-- Prove2me | Theorems.Thm_BauerleRiederMDP_TransactionCosts_theorem_4_5_4
-- name    : BauerleRiederMDP.TransactionCosts.theorem_4_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:33:12.373821+00:00
-- url     : https://prove2.me/theorems/76a53807-a85b-45ad-9afa-25bea291e208
-- title:
--   Theorem 4.5.4 — concave homogeneous value functions and the buy/hold/sell optimal policy (4.32)
-- statement:
--   Consider the terminal wealth problem with proportional transaction costs of §4.5 under its standing assumptions: $0\le c<1$, $i_n\ge0$, independent $\tilde R_n>0$ with $\mathbb E\|\tilde R_n\|<\infty$, and a utility function $U$ on $[0,\infty)$ that is homogeneous of degree $\gamma$. Let $V_n$ be the value functions, $h$ the upper boundary of $D(x)$, and $q_\pm(V_{n+1})$ the thresholds (4.30)–(4.31). Then:
--
--   1. (a) For $n=0,\dots,N$ the value function $V_n$ is concave, increasing and homogeneous of degree $\gamma$ on $E$, and for $x=(x_0,x_1)\in E$
--   $$V_N(x)=U(x_0+x_1),\qquad V_n(x)=\sup_{0\le a\le x_1+\frac{x_0}{1+c}}\mathbb E\,V_{n+1}\big(h(x,a)(1+i_{n+1}),\ a\tilde R_{n+1}\big).$$
--   2. (b) The optimal amount invested in the stock at time $n$ is
--   $$f^*_n(x)=\begin{cases}\dfrac{x_0+(1-c)x_1}{1+(1-c)q_+(V_{n+1})}\,q_+(V_{n+1}), & \frac{x_1}{x_0}>q_+(V_{n+1}),\\[4pt] x_1, & q_-(V_{n+1})\le\frac{x_1}{x_0}\le q_+(V_{n+1}),\\[4pt] \dfrac{x_0+(1+c)x_1}{1+(1+c)q_-(V_{n+1})}\,q_-(V_{n+1}), & \frac{x_1}{x_0}<q_-(V_{n+1}),\end{cases}\tag{4.32}$$
--   and the optimal amount invested in the bond at time $n$ is $h(x,f^*_n(x))$: the policy $\pi^*_n(x)=(h(x,f^*_n(x)),f^*_n(x))$ is a Markov policy with $V_{n\pi^*}=V_n$ on $E$ for every $n\le N$.
--
--   In addition, for every $n<N$ the selling problem at $(0,1)$ and the buying problem at $(1,0)$ have largest maximum points $a_\pm$, from which $q_\pm(V_{n+1})$ are computed, and $q_-(V_{n+1})\le q_+(V_{n+1})$, so the three regions of (4.32) are disjoint.
--
--   The theorem shows that with proportional transaction costs the optimal portfolio is described by two cones in the $(x_0,x_1)$ plane: sell stock down to the ratio $q_+$ above it, buy up to $q_-$ below it, and do not trade in between.
--
--   **Formalization Note** Value functions are `EReal`-valued and $V_n$ is the supremum over all Markov policies choosing both holdings $(a_0,a_1)\in D(x)$; the reduction to the upper boundary $a_0=h(x,a)$ is part of the statement (the Bellman equation in a)).
--
--   Differences from the source:
--   - reading: q₊(v), q₋(v) := argmax_{q≥0} of (4.30)–(4.31) → q± computed by (4.28)–(4.29) from the largest maximum points a± of the equivalent problems on [0,1] and [0,1/(1+c)]; reason: the argmax is not attained when a₊ = 1 (q₊ = ∞) and need not be unique; the proof of Theorem 4.5.4 gives the transformation; paper.md reading 3
--   - reading: (4.32) buy case with q₋(V_{n+1}) = ∞ (printed fraction ∞/∞) → value (x₀ + (1+c)x₁)/(1+c), the limit of the printed fraction; reason: the proof's (x₀ + (1+c)x₁)a₋ with a₋ = 1/(1+c), step (v), p.111
--   - generalization: existence of the largest maximum points a± and q₋ ≤ q₊ (used in the proof, steps (ii), (iv), (vi) of Proposition 4.5.2) → asserted as additional conclusions (IsGreatest of the argmax sets, qMinus ≤ qPlus); reason: extra conclusions; dropping them gives the printed statement
--   - generalization: π* optimal: V_{0π*} = V_0 on E (definition of optimality, p.18) → π* is a Markov policy and V_{nπ*} = V_n on E for every n ≤ N; reason: n = 0 is the printed claim
--   - encoding: x₁/x₀, with x₀ = 0 allowed → ratio in [0, ∞] with x₁/0 = ∞ for x₁ > 0 and value 0 at (0,0); reason: at (0,0) every branch of (4.32) gives 0, the only admissible stock amount
--   - encoding: functions E → [−∞, ∞) and their expectations → EReal-valued functions; expectation IE f⁺ − IE f⁻ in EReal (eexp); reason: Lean convention; same instances, and every expectation used exists
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 4.5.4, p.113 (PDF 127); eqs. (4.28)–(4.31), pp.110–112 (PDF 124–126)

import Mathlib
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_Assumptions
import Definitions.Def_BauerleRiederMDP_TransactionCosts_stateSpace
import Definitions.Def_BauerleRiederMDP_TransactionCosts_bondAfter
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_Lop
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_IsPolicy
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_Vpi
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_V
import Definitions.Def_BauerleRiederMDP_TransactionCosts_IncreasingOnE
import Definitions.Def_BauerleRiederMDP_TransactionCosts_ConcaveOnE
import Definitions.Def_BauerleRiederMDP_TransactionCosts_HomogeneousOfDegree
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_argmaxPlus
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_argmaxMinus
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_aPlus
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_aMinus
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_qPlus
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_qMinus
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_optimalPolicy

open scoped ENNReal

namespace BauerleRiederMDP.TransactionCosts

/-- Theorem 4.5.4 of Bäuerle & Rieder (2011), *Markov Decision Processes with Applications to
Finance*, p.113 (PDF 127). For the terminal wealth problem with transaction costs (§4.5, under
its standing assumptions):

a) the value functions `V_n` (`n = 0, …, N`) are concave, increasing and homogeneous of degree
`γ` on `E`, and for `x = (x₀, x₁) ∈ E`
`V_N(x) = U(x₀ + x₁)` and
`V_n(x) = sup_{0 ≤ a ≤ x₁ + x₀/(1+c)} IE V_{n+1}(h(x, a)(1 + i_{n+1}), a R̃_{n+1})`;

b) the optimal amount invested in the stock at time `n` is `f*_n(x)` of (4.32), with the
thresholds `q₊(V_{n+1})`, `q₋(V_{n+1})` of (4.30)–(4.31), and the optimal amount invested in the
bond at time `n` is `h(x, f*_n(x))`: the policy `x ↦ (h(x, f*_n(x)), f*_n(x))` is a Markov
policy and attains `V_n` on `E`.

The thresholds are those of the proof: for every `n < N` the selling problem at `(0, 1)` and the
buying problem at `(1, 0)` have largest maximum points `a₊`, `a₋`, from which `q₊`, `q₋` are
computed by (4.28)–(4.29); and `q₋(V_{n+1}) ≤ q₊(V_{n+1})` (step (vi) of the proof of
Proposition 4.5.2), so the three regions of (4.32) are disjoint.

**Formalization Note.** Value functions are `EReal`-valued and `V_n` is the supremum over all
Markov policies of decision rules `(a₀, a₁) ∈ D(x)` (4.23) (not only those on the upper boundary
`a₀ = h(x, a₁)`). Optimality is stated for every starting time `n ≤ N` (for `n = 0` it is the
book's definition of an optimal policy, p.18). -/
theorem theorem_4_5_4 {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω) (hM : M.Assumptions) :
    (∀ n ≤ M.N, ConcaveOnE (M.V n) ∧ IncreasingOnE (M.V n) ∧
      HomogeneousOfDegree M.γ (M.V n)) ∧
    (∀ x ∈ stateSpace, M.V M.N x = ((M.U (x.1 + x.2) : ℝ) : EReal)) ∧
    (∀ n < M.N, ∀ x ∈ stateSpace,
      M.V n x = ⨆ a ∈ Set.Icc (0 : ℝ) (x.2 + x.1 / (1 + M.c)),
        M.Lop n (M.V (n + 1)) x (bondAfter M.c x a, a)) ∧
    (∀ n < M.N,
      IsGreatest (M.argmaxPlus n (M.V (n + 1))) (M.aPlus n (M.V (n + 1))) ∧
      IsGreatest (M.argmaxMinus n (M.V (n + 1))) (M.aMinus n (M.V (n + 1))) ∧
      M.qMinus n (M.V (n + 1)) ≤ M.qPlus n (M.V (n + 1))) ∧
    M.IsPolicy 0 M.optimalPolicy ∧
    ∀ n ≤ M.N, ∀ x ∈ stateSpace, M.Vpi M.optimalPolicy n x = M.V n x := by sorry

end BauerleRiederMDP.TransactionCosts
