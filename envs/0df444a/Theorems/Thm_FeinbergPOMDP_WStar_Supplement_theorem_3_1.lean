-- Prove2me | Theorems.Thm_FeinbergPOMDP_WStar_Supplement_theorem_3_1
-- name    : FeinbergPOMDP.WStar.Supplement.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:24:03.677257+00:00
-- url     : https://prove2.me/theorems/c444c618-fb01-4f82-a72d-8099ba7f7eb3
-- title:
--   Theorem 3.1 (corrected: nonempty 𝔸) — under (D) or (P), Assumption (W*) for the COMDP gives optimality equations, optimal policies and convergence of value iterations
-- statement:
--   Here $\mathbb X,\mathbb Y,\mathbb A$ are the state, observation and action spaces, $P(dx'|x,a)$ the transition kernel, $Q(dy|a,x)$ the observation kernel, $c(x,a)$ the bounded-below one-step cost with values in $\overline{\mathbb R}=\mathbb R\cup\{+\infty\}$, and $\alpha\ge0$ the discount factor. The COMDP is the MDP $(\mathbb P(\mathbb X),\mathbb A,q,\bar c)$ on beliefs $z\in\mathbb P(\mathbb X)$ (weak topology), with cost $\bar c(z,a)=\int_{\mathbb X}c(x,a)\,z(dx)$ (3.8) and transition probability $q(D|z,a)=\int_{\mathbb Y}\mathbf 1\{H(z,a,y)\in D\}\,R'(dy|z,a)$ (3.5), where $R'$ (3.2) is the law of the next observation and $H$ a filter satisfying (3.3). Its optimal values $\bar v_{t,\alpha}$ and $\bar v_\alpha$ are infima of the expected total discounted costs over all I-policies (randomized, history-dependent policies of the COMDP).
--
--   **Theorem 3.1.** Assume either (D) ($c$ bounded below and $0\le\alpha<1$) or (P) ($c\ge0$ and $0\le\alpha\le1$), and that the COMDP satisfies Assumption (W*): $\bar c$ is $\mathbb K$-inf-compact on $\mathbb P(\mathbb X)\times\mathbb A$ and $q(\cdot|z,a)$ is weakly continuous in $(z,a)$. Then:
--
--   1. $\bar v_{t,\alpha}$ ($t=0,1,\dots$) and $\bar v_\alpha$ are lower semi-continuous on $\mathbb P(\mathbb X)$, and $\bar v_{t,\alpha}(z)\to\bar v_\alpha(z)$ for every $z$.
--   2. For every $z$ and $t$, with $\bar v_{0,\alpha}=0$,
--   $$\bar v_{t+1,\alpha}(z)=\min_{a\in\mathbb A}\Big\{\bar c(z,a)+\alpha\int_{\mathbb P(\mathbb X)}\bar v_{t,\alpha}(z')\,q(dz'|z,a)\Big\}=\min_{a\in\mathbb A}\Big\{\int_{\mathbb X}c(x,a)z(dx)+\alpha\int_{\mathbb X}\int_{\mathbb X}\int_{\mathbb Y}\bar v_{t,\alpha}(H(z,a,y))\,Q(dy|a,x')P(dx'|x,a)z(dx)\Big\},$$
--   and the sets $A_{t,\alpha}(z)$ of minimizers of the first expression are nonempty, have a Borel graph, equal $\mathbb A$ when $\bar v_{t+1,\alpha}(z)=+\infty$ and are compact when $\bar v_{t+1,\alpha}(z)<+\infty$.
--   3. For every $T\ge1$ there is an optimal Markov $T$-horizon I-policy, and every Markov policy with $\varphi_{T-1-t}(z)\in A_{t,\alpha}(z)$ for all $z$ and $t=0,\dots,T-1$ is $T$-horizon optimal.
--   4. The same equation (3.11) holds for $\bar v_\alpha$ with minimizer sets $A_\alpha(z)$ having the same four properties.
--   5. There is a stationary discount-optimal I-policy, and a stationary I-policy $\varphi$ is optimal if and only if $\varphi(z)\in A_\alpha(z)$ for all $z$.
--   6. If $\bar c$ is inf-compact on $\mathbb P(\mathbb X)\times\mathbb A$, then $\bar v_{t,\alpha}$ ($t\ge1$) and $\bar v_\alpha$ are inf-compact on $\mathbb P(\mathbb X)$.
--
--   This is Theorem 2.1 for MDPs, applied to the COMDP; it is what makes Assumption (W*) for the COMDP the target of the paper's main theorems.
--
--   **Formalization Note** The cost is $c=\ell+f$ with $f\ge0$ extended-real valued, so that $\bar c=\ell+\int f\,dz$. The statements are made for the COMDP built from a filter $H$ satisfying (3.3). The action set is assumed nonempty.
--
--   Differences from the source:
--   - encoding: 𝕏, 𝕐, 𝔸 are Borel subsets of Polish spaces → separable metrizable spaces with Borel σ-algebras that are standard Borel (PolishSpace not assumed); reason: a separable metrizable space is (homeomorphic to) a Borel subset of a Polish space exactly when its Borel σ-algebra is standard; same instances
--   - encoding: bounded-below Borel cost c : 𝕏 × 𝔸 → ℝ ∪ {+∞}; c̄(z,a) = ∫ c(x,a) z(dx) → c = lower + f with lower : ℝ and Borel f : 𝕏 → 𝔸 → [0,∞]; c̄ = lower + ∫⁻ f(·,a) dz, in EReal; reason: every bounded-below ℝ ∪ {+∞}-valued Borel function has this form; the integral is exact also when c = +∞ on a z-positive set
--   - encoding: expected total discounted costs E Σ α^t c(z_t,a_t) of I-policies, optimal values as infima, integrals of v̄ against q, and 'min' → expectations under the Ionescu Tulcea strategic measure of the published FeinbergLiang.ACOE.MDP, as positive part minus negative part in EReal; 'v = min_a g(a)' as 'some a₀ attains v and v ≤ g(a) for all a'; Markov policies as ℕ-indexed sequences of Borel maps; reason: under (D) the negative parts have finite expectation and under (P) they vanish, so no ∞ − ∞ occurs and these are the paper's quantities; a T-horizon cost does not depend on decision rules after T
--   - encoding: q(D|z,a) = ∫ I{H(z,a,y) ∈ D} R′(dy|z,a) for a stochastic kernel H satisfying (3.3), whose choice does not affect q → statements about q are made for a filter H with IsFilter P Q H (for every such H in the conclusions); the COMDP kernel is q packaged as a Kernel on (ℙ(𝕏), its Borel σ-algebra); reason: p. 8: the choice of H does not affect q; the measurability of (z,a) ↦ q(·|z,a) holds for every filter, so the packaging is exactly q
--   - encoding: Gr(A_{t,α}), Gr(A_α) are Borel subsets of ℙ(𝕏) × 𝔸 → measurable in the product of the Borel σ-algebras of ℙ(𝕏) and 𝔸; reason: both spaces are second countable, so the product σ-algebra is the Borel σ-algebra of the product
--   - correction: no explicit nonemptiness of the action set 𝔸 → [Nonempty 𝔸]; reason: the COMDP has the action set 𝔸 at every state (p. 9, (ii)); for 𝔸 = ∅ and 𝕏 ≠ ∅ the claimed nonempty sets A_{t,α}(z) do not exist, so (ii) is false as printed; the added premise excludes only that case
-- source:
--   Feinberg, Kasyanov, Zgurovsky, Partially Observable Total-Cost Markov Decision Processes with Weakly Continuous Transition Probabilities, arXiv:1401.2168v2, Theorem 3.1, p. 10 (proof: the sentence before it, p. 9, applying Theorem 2.1, pp. 6–7)

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_FeinbergPOMDP_WStar_Model
import Definitions.Def_FeinbergPOMDP_WStar_Supplement_MDPValues
import Definitions.Def_FeinbergPOMDP_WStar_Supplement_COMDP

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter FeinbergLiang.ACOE FeinbergPOMDP.WStar

namespace FeinbergPOMDP.WStar.Supplement

/-- Feinberg, Kasyanov, Zgurovsky, arXiv:1401.2168v2, **Theorem 3.1** (p. 10; proved on p. 9 by
applying Theorem 2.1 to the COMDP): under (D) or (P), if the COMDP `(ℙ(𝕏), 𝔸, q, c̄)` satisfies
Assumption (W*) (`c̄` is `𝕂`-inf-compact on `ℙ(𝕏) × 𝔸` and `q` is weakly continuous), then
statements (i)–(vi) hold (`COMDPOptimality`).

Formalization Note. `𝕏, 𝕐, 𝔸` are Borel subsets of Polish spaces (p. 4), encoded as separable metrizable spaces
whose Borel σ-algebras are standard Borel (equivalently, Borel subsets of their completions;
`PolishSpace` is not assumed). The cost `c : 𝕏 × 𝔸 → ℝ ∪ {+∞}`, bounded below and Borel (p. 4), is
written `c(x, a) = lower + f x a` with `lower : ℝ` and `f : 𝕏 → 𝔸 → [0, ∞]` Borel, so that
`c̄(z, a) = lower + beliefCost f z a` (3.8). (D) is `0 ≤ α < 1`; (P) is `c ≥ 0` and `0 ≤ α ≤ 1`.
`q` is built from a filter `H` satisfying (3.3) (`IsFilter`); its choice does not affect `q` (p. 8).
`𝔸` is assumed nonempty: the COMDP has the action set `𝔸` at every state, and for `𝔸 = ∅` (with
`𝕏 ≠ ∅`) the nonemptiness of `A_{t,α}(z)` claimed in (ii) fails. -/
theorem theorem_3_1 {X Y A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X]
    [TopologicalSpace Y] [TopologicalSpace.MetrizableSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] [StandardBorelSpace Y]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A]
    [Nonempty A]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y) [IsMarkovKernel Q]
    (H : ProbabilityMeasure X → A → Y → ProbabilityMeasure X) (hH : IsFilter P Q H)
    (lower α : ℝ) (f : X → A → ℝ≥0∞) (hf : Measurable (Function.uncurry f))
    (hDP : (0 ≤ α ∧ α < 1) ∨
      ((∀ (x : X) (a : A), (0 : EReal) ≤ (lower : EReal) + (f x a : EReal)) ∧ 0 ≤ α ∧ α ≤ 1))
    (hW₁ : KInfCompact (beliefCost f)) (hW₂ : BeliefTransitionWeaklyContinuous P Q H) :
    COMDPOptimality P Q H lower f α := by sorry

end FeinbergPOMDP.WStar.Supplement
