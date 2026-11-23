-- Prove2me | Theorems.Thm_FeinbergPOMDP_WStar_Supplement_theorem_3_2
-- name    : FeinbergPOMDP.WStar.Supplement.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:25:01.754822+00:00
-- url     : https://prove2.me/theorems/5f20951a-580d-42b9-985d-0b189570e7ab
-- title:
--   Theorem 3.2 (corrected: nonempty 𝔸) — 𝕂-inf-compact c and either continuity condition (c)(i) or (c)(ii) give (W*) for the COMDP and the conclusions of Theorem 3.1
-- statement:
--   Here $\mathbb X,\mathbb Y,\mathbb A$ are the state, observation and action spaces, $P(dx'|x,a)$ the transition kernel, $Q(dy|a,x)$ the observation kernel, $c(x,a)$ the bounded-below one-step cost with values in $\overline{\mathbb R}=\mathbb R\cup\{+\infty\}$, and $\alpha\ge0$ the discount factor. The COMDP is the MDP $(\mathbb P(\mathbb X),\mathbb A,q,\bar c)$ on beliefs $z\in\mathbb P(\mathbb X)$ (weak topology), with cost $\bar c(z,a)=\int_{\mathbb X}c(x,a)\,z(dx)$ (3.8) and transition probability $q(D|z,a)=\int_{\mathbb Y}\mathbf 1\{H(z,a,y)\in D\}\,R'(dy|z,a)$ (3.5), where $R'$ (3.2) is the law of the next observation and $H$ a filter satisfying (3.3). Its optimal values $\bar v_{t,\alpha}$ and $\bar v_\alpha$ are infima of the expected total discounted costs over all I-policies (randomized, history-dependent policies of the COMDP).
--
--   **Theorem 3.2.** Assume
--   1. (a) either (D) or (P);
--   2. (b) $c$ is $\mathbb K$-inf-compact on $\mathbb X\times\mathbb A$;
--   3. (c) either (i) the observation kernel $R'(dy|z,a)$ is setwise continuous and Assumption (H) holds, or (ii) $P$ and $Q$ are weakly continuous and some weakly continuous stochastic kernel $H$ on $\mathbb X$ given $\mathbb P(\mathbb X)\times\mathbb A\times\mathbb Y$ satisfies (3.3).
--
--   Then the COMDP satisfies Assumption (W*): $\bar c$ is $\mathbb K$-inf-compact on $\mathbb P(\mathbb X)\times\mathbb A$ and $q$ is weakly continuous; and therefore:
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
--   This is one of the paper's two main results: it gives conditions on the POMDP itself under which its COMDP has optimal policies.
--
--   **Formalization Note** The cost is $c=\ell+f$ with $f\ge0$; $\bar c\ge\ell$ holds by construction and is not restated. The weak continuity of $q$ and statements (i)–(vi) are concluded for every filter satisfying (3.3), since its choice does not affect $q$. The action set is assumed nonempty.
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
--   Feinberg, Kasyanov, Zgurovsky, Partially Observable Total-Cost Markov Decision Processes with Weakly Continuous Transition Probabilities, arXiv:1401.2168v2, Theorem 3.2, p. 11 (proof p. 24)

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_FeinbergPOMDP_WStar_Model
import Definitions.Def_FeinbergPOMDP_WStar_Supplement_MDPValues
import Definitions.Def_FeinbergPOMDP_WStar_Supplement_COMDP

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter FeinbergLiang.ACOE FeinbergPOMDP.WStar

namespace FeinbergPOMDP.WStar.Supplement

/-- Feinberg, Kasyanov, Zgurovsky, arXiv:1401.2168v2, **Theorem 3.2** (p. 11; proof p. 24): if
(a) (D) or (P) holds, (b) `c` is `𝕂`-inf-compact on `𝕏 × 𝔸`, and (c) either (i) `R′(dy | z, a)` is
setwise continuous and Assumption (H) holds, or (ii) `P` and `Q` are weakly continuous and some
weakly continuous stochastic kernel `H` on `𝕏` given `ℙ(𝕏) × 𝔸 × 𝕐` satisfies (3.3), then the
COMDP satisfies Assumption (W*) (`c̄` is `𝕂`-inf-compact and `q` is weakly continuous) and
statements (i)–(vi) of Theorem 3.1 hold.

Formalization Note. `𝕏, 𝕐, 𝔸` are Borel subsets of Polish spaces (p. 4), encoded as separable metrizable spaces
whose Borel σ-algebras are standard Borel (equivalently, Borel subsets of their completions;
`PolishSpace` is not assumed). The cost `c : 𝕏 × 𝔸 → ℝ ∪ {+∞}`, bounded below and Borel (p. 4), is
written `c(x, a) = lower + f x a` with `lower : ℝ` and `f : 𝕏 → 𝔸 → [0, ∞]` Borel, so that
`c̄(z, a) = lower + beliefCost f z a` (3.8). (D) is `0 ≤ α < 1`; (P) is `c ≥ 0` and `0 ≤ α ≤ 1`.
`𝕂`-inf-compactness is the published `FeinbergLiang.ACOE.KInfCompact` of `f` (equivalent to the
paper's definition on p. 6, since `lower + ·` only shifts levels). `q` is built from a filter `H`
satisfying (3.3); its choice does not affect `q` (p. 8), so the conclusions are stated for every
such `H`. `c̄ ≥ lower` holds by construction. `𝔸` is assumed nonempty, as in Theorem 3.1. -/
theorem theorem_3_2 {X Y A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X]
    [TopologicalSpace Y] [TopologicalSpace.MetrizableSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] [StandardBorelSpace Y]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A]
    [Nonempty A]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y) [IsMarkovKernel Q]
    (lower α : ℝ) (f : X → A → ℝ≥0∞) (hf : Measurable (Function.uncurry f))
    (hDP : (0 ≤ α ∧ α < 1) ∨
      ((∀ (x : X) (a : A), (0 : EReal) ≤ (lower : EReal) + (f x a : EReal)) ∧ 0 ≤ α ∧ α ≤ 1))
    (hK : KInfCompact f)
    (hc : (IsSetwiseContinuous (fun p : ProbabilityMeasure X × A => obsLaw P Q p.1 p.2) ∧
            AssumptionH P Q) ∨
          (IsWeaklyContinuous (kernelPM P) ∧ IsWeaklyContinuous (kernelPM Q) ∧
            ∃ H₀ : ProbabilityMeasure X → A → Y → ProbabilityMeasure X, IsFilter P Q H₀ ∧
              IsWeaklyContinuous (fun p : ProbabilityMeasure X × A × Y => H₀ p.1 p.2.1 p.2.2))) :
    KInfCompact (beliefCost f) ∧
    ∀ H : ProbabilityMeasure X → A → Y → ProbabilityMeasure X, IsFilter P Q H →
      BeliefTransitionWeaklyContinuous P Q H ∧ COMDPOptimality P Q H lower f α := by sorry

end FeinbergPOMDP.WStar.Supplement
