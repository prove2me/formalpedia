-- Prove2me | Theorems.Thm_FeinbergPOMDP_WStar_Supplement_theorem_7_1
-- name    : FeinbergPOMDP.WStar.Supplement.theorem_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:29:08.931333+00:00
-- url     : https://prove2.me/theorems/1f999497-a3df-4742-997a-7b951bf2e2cb
-- title:
--   Theorem 7.1 (corrected: nonempty 𝔸) — weak continuity of H on an open part 𝕐₁ and Assumption (H) on 𝕐₂ give weakly continuous q, (W*) and Theorem 3.1
-- statement:
--   Here $\mathbb X,\mathbb Y,\mathbb A$ are the state, observation and action spaces, $P(dx'|x,a)$ the transition kernel, $Q(dy|a,x)$ the observation kernel, $c(x,a)$ the bounded-below one-step cost with values in $\overline{\mathbb R}=\mathbb R\cup\{+\infty\}$, and $\alpha\ge0$ the discount factor. The COMDP is the MDP $(\mathbb P(\mathbb X),\mathbb A,q,\bar c)$ on beliefs $z\in\mathbb P(\mathbb X)$ (weak topology), with cost $\bar c(z,a)=\int_{\mathbb X}c(x,a)\,z(dx)$ (3.8) and transition probability $q(D|z,a)=\int_{\mathbb Y}\mathbf 1\{H(z,a,y)\in D\}\,R'(dy|z,a)$ (3.5), where $R'$ (3.2) is the law of the next observation and $H$ a filter satisfying (3.3). Its optimal values $\bar v_{t,\alpha}$ and $\bar v_\alpha$ are infima of the expected total discounted costs over all I-policies (randomized, history-dependent policies of the COMDP).
--
--   **Theorem 7.1.** Let $\mathbb Y=\mathbb Y_1\cup\mathbb Y_2$ be a partition with $\mathbb Y_1$ open in $\mathbb Y$. Assume:
--   1. (a) $P$ and $Q$ are weakly continuous;
--   2. (b) the restriction of $R'(\cdot|z,a)$ to $(\mathbb Y_2,\mathcal B(\mathbb Y_2))$ is setwise continuous: $R'(C|z^{(n)},a^{(n)})\to R'(C|z,a)$ whenever $(z^{(n)},a^{(n)})\to(z,a)$ and $C\in\mathcal B(\mathbb Y_2)$;
--   3. (c) some filter $H$ satisfying (3.3) is (i) weakly continuous on $\mathbb P(\mathbb X)\times\mathbb A\times\mathbb Y_1$ and (ii) satisfies Assumption (H) on $\mathbb Y_2$: whenever $z^{(n)}\to z$ weakly and $a^{(n)}\to a$, there are a subsequence $(z^{(n_k)},a^{(n_k)})$ and a measurable $C\subseteq\mathbb Y_2$ with $R'(\mathbb Y_2\setminus C|z,a)=0$ such that $H(z^{(n_k)},a^{(n_k)},y)\to H(z,a,y)$ weakly for all $y\in C$.
--
--   Then $q$ is weakly continuous. If moreover (D) or (P) holds and $c$ is $\mathbb K$-inf-compact on $\mathbb X\times\mathbb A$, then the COMDP satisfies Assumption (W*) and:
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
--   The theorem covers models in which the filter is continuous for some observations and only almost surely convergent along subsequences for others, such as the inventory models of §8.2.
--
--   **Formalization Note** $\mathbb Y_2$ is the complement of $\mathbb Y_1$; its Borel sets are the Borel subsets of $\mathbb Y$ contained in it. The weak continuity of $q$ and statements (i)–(vi) are concluded for every filter satisfying (3.3). The action set is assumed nonempty in the second part.
--
--   Differences from the source:
--   - encoding: 𝕏, 𝕐, 𝔸 are Borel subsets of Polish spaces → separable metrizable spaces with Borel σ-algebras that are standard Borel (PolishSpace not assumed); reason: a separable metrizable space is (homeomorphic to) a Borel subset of a Polish space exactly when its Borel σ-algebra is standard; same instances
--   - encoding: bounded-below Borel cost c : 𝕏 × 𝔸 → ℝ ∪ {+∞}; c̄(z,a) = ∫ c(x,a) z(dx) → c = lower + f with lower : ℝ and Borel f : 𝕏 → 𝔸 → [0,∞]; c̄ = lower + ∫⁻ f(·,a) dz, in EReal; reason: every bounded-below ℝ ∪ {+∞}-valued Borel function has this form; the integral is exact also when c = +∞ on a z-positive set
--   - encoding: c is 𝕂-inf-compact on 𝕏 × 𝔸 (p. 6) → FeinbergLiang.ACOE.KInfCompact f (nonempty compact K, levels l ∈ ℝ≥0 of f); reason: empty K gives empty level sets and the shift by lower maps real levels of c to levels of f; equivalent
--   - encoding: expected total discounted costs E Σ α^t c(z_t,a_t) of I-policies, optimal values as infima, integrals of v̄ against q, and 'min' → expectations under the Ionescu Tulcea strategic measure of the published FeinbergLiang.ACOE.MDP, as positive part minus negative part in EReal; 'v = min_a g(a)' as 'some a₀ attains v and v ≤ g(a) for all a'; Markov policies as ℕ-indexed sequences of Borel maps; reason: under (D) the negative parts have finite expectation and under (P) they vanish, so no ∞ − ∞ occurs and these are the paper's quantities; a T-horizon cost does not depend on decision rules after T
--   - encoding: q(D|z,a) = ∫ I{H(z,a,y) ∈ D} R′(dy|z,a) for a stochastic kernel H satisfying (3.3), whose choice does not affect q → statements about q are made for a filter H with IsFilter P Q H (for every such H in the conclusions); the COMDP kernel is q packaged as a Kernel on (ℙ(𝕏), its Borel σ-algebra); reason: p. 8: the choice of H does not affect q; the measurability of (z,a) ↦ q(·|z,a) holds for every filter, so the packaging is exactly q
--   - encoding: Gr(A_{t,α}), Gr(A_α) are Borel subsets of ℙ(𝕏) × 𝔸 → measurable in the product of the Borel σ-algebras of ℙ(𝕏) and 𝔸; reason: both spaces are second countable, so the product σ-algebra is the Borel σ-algebra of the product
--   - correction: no explicit nonemptiness of the action set 𝔸 → [Nonempty 𝔸]; reason: the COMDP has the action set 𝔸 at every state (p. 9, (ii)); for 𝔸 = ∅ and 𝕏 ≠ ∅ the claimed nonempty sets A_{t,α}(z) do not exist, so (ii) is false as printed; the added premise excludes only that case
-- source:
--   Feinberg, Kasyanov, Zgurovsky, Partially Observable Total-Cost Markov Decision Processes with Weakly Continuous Transition Probabilities, arXiv:1401.2168v2, Theorem 7.1, p. 25 (proof pp. 25–26)

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_FeinbergPOMDP_WStar_Model
import Definitions.Def_FeinbergPOMDP_WStar_Supplement_MDPValues
import Definitions.Def_FeinbergPOMDP_WStar_Supplement_COMDP

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter FeinbergLiang.ACOE FeinbergPOMDP.WStar

namespace FeinbergPOMDP.WStar.Supplement

/-- Feinberg, Kasyanov, Zgurovsky, arXiv:1401.2168v2, **Theorem 7.1** (p. 25; proof pp. 25–26): let
`𝕐 = 𝕐₁ ∪ 𝕐₂` be a partition with `𝕐₁` open in `𝕐`. If (a) `P` and `Q` are weakly continuous,
(b) `R′(· | z, a)` restricted to `𝕐₂` is setwise continuous in `(z, a)`, and (c) some filter `H`
satisfying (3.3) is (i) weakly continuous on `ℙ(𝕏) × 𝔸 × 𝕐₁` and (ii) satisfies Assumption (H) on
`𝕐₂`, then `q` is weakly continuous. If moreover (a) and (b) of Theorem 3.2 hold ((D) or (P), and
`c` `𝕂`-inf-compact), the COMDP satisfies Assumption (W*) and statements (i)–(vi) of Theorem 3.1 hold.

Formalization Note. `𝕏, 𝕐, 𝔸` are Borel subsets of Polish spaces (p. 4), encoded as separable metrizable spaces
whose Borel σ-algebras are standard Borel (equivalently, Borel subsets of their completions;
`PolishSpace` is not assumed). The cost `c : 𝕏 × 𝔸 → ℝ ∪ {+∞}`, bounded below and Borel (p. 4), is
written `c(x, a) = lower + f x a` with `lower : ℝ` and `f : 𝕏 → 𝔸 → [0, ∞]` Borel, so that
`c̄(z, a) = lower + beliefCost f z a` (3.8). (D) is `0 ≤ α < 1`; (P) is `c ≥ 0` and `0 ≤ α ≤ 1`.
`𝕐₂` is the complement of `𝕐₁`; the Borel sets of the subspace `𝕐₂` are the Borel sets of `𝕐`
contained in `𝕐₂` (`𝕐₂` is closed). Condition (c)(i) is the weak continuity (p. 4) of
`(z, a, y) ↦ H(z, a, y)` on the subspace `ℙ(𝕏) × 𝔸 × 𝕐₁`. Weak continuity of `q` is stated for
every filter (its choice does not affect `q`, p. 8), while (c) is about one filter. `𝔸` is assumed
nonempty in the second part, as in Theorem 3.1. -/
theorem theorem_7_1 {X Y A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X]
    [TopologicalSpace Y] [TopologicalSpace.MetrizableSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] [StandardBorelSpace Y]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y) [IsMarkovKernel Q]
    (Y₁ : Set Y) (hY₁ : IsOpen Y₁)
    (ha : IsWeaklyContinuous (kernelPM P) ∧ IsWeaklyContinuous (kernelPM Q))
    (hb : ObsLawSetwiseContinuousOn P Q Y₁ᶜ)
    (hc : ∃ H₀ : ProbabilityMeasure X → A → Y → ProbabilityMeasure X, IsFilter P Q H₀ ∧
      IsWeaklyContinuous (fun p : ProbabilityMeasure X × A × Y₁ => H₀ p.1 p.2.1 p.2.2) ∧
      FilterSubseqOn P Q H₀ Y₁ᶜ) :
    (∀ H : ProbabilityMeasure X → A → Y → ProbabilityMeasure X, IsFilter P Q H →
      BeliefTransitionWeaklyContinuous P Q H) ∧
    (∀ [Nonempty A] (lower α : ℝ) (f : X → A → ℝ≥0∞), Measurable (Function.uncurry f) →
      ((0 ≤ α ∧ α < 1) ∨
        ((∀ (x : X) (a : A), (0 : EReal) ≤ (lower : EReal) + (f x a : EReal)) ∧ 0 ≤ α ∧ α ≤ 1)) →
      KInfCompact f →
      KInfCompact (beliefCost f) ∧
      ∀ H : ProbabilityMeasure X → A → Y → ProbabilityMeasure X, IsFilter P Q H →
        BeliefTransitionWeaklyContinuous P Q H ∧ COMDPOptimality P Q H lower f α) := by sorry

end FeinbergPOMDP.WStar.Supplement
