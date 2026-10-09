-- Prove2me | Theorems.Thm_FeinbergPOMDP_WStar_theorem_3_6
-- name    : FeinbergPOMDP.WStar.theorem_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:56:08.575831+00:00
-- url     : https://prove2.me/theorems/ef54387d-2b8e-4f4d-adce-a1844e3004a6
-- title:
--   Theorem 3.6 — weakly continuous P and total-variation-continuous Q make the COMDP satisfy Assumption (W*)
-- statement:
--   Let $\mathbb X, \mathbb Y, \mathbb A$ be Borel subsets of Polish spaces and consider a POMDP with transition kernel $P(dx' \mid x, a)$, observation kernel $Q(dy \mid a, x)$ and one-step cost $c : \mathbb X \times \mathbb A \to \mathbb R \cup \{+\infty\}$. Its belief MDP (COMDP) has state space $\mathbb P(\mathbb X)$ with the weak topology, action set $\mathbb A$, cost $\bar c(z, a) = \int c(x, a)\,z(dx)$ (3.8) and transition $q(\cdot \mid z, a)$, the law of the posterior $H(z, a, y)$ when $y \sim R'(\cdot \mid z, a)$ (3.5).
--
--   Assume:
--
--   1. either Assumption (D) holds ($0 \le \alpha < 1$), or Assumption (P) holds ($c \ge 0$ and $0 \le \alpha \le 1$);
--   2. $c$ is Borel, bounded below and $\mathbb K$-inf-compact on $\mathbb X \times \mathbb A$;
--   3. $P$ is weakly continuous;
--   4. $Q$ is continuous in the total variation.
--
--   Then the COMDP satisfies Assumption (W*):
--
--   1. $\bar c$ is bounded below by every lower bound of $c$, and $\bar c$ is $\mathbb K$-inf-compact on $\mathbb P(\mathbb X) \times \mathbb A$;
--   2. $q(\cdot \mid z, a)$ is weakly continuous in $(z, a) \in \mathbb P(\mathbb X) \times \mathbb A$: for every filter $H$ satisfying (3.3), $z^{(n)} \to z$ weakly and $a^{(n)} \to a$ imply
--   $$\int g\,dq(\cdot \mid z^{(n)}, a^{(n)}) \to \int g\,dq(\cdot \mid z, a)\quad\text{for every bounded continuous } g : \mathbb P(\mathbb X) \to \mathbb R .$$
--
--   Assumption (W*) is the hypothesis under which the general theory of MDPs with weakly continuous transitions (Feinberg et al. 2012) yields optimality equations, convergence of value iterations and stationary optimal policies, so the theorem gives these for the POMDP in terms of its primitive data.
--
--   **Formalization Note.** The cost is written $c = \ell + f$ with $\ell \in \mathbb R$ and $f$ Borel with values in $[0, \infty]$; $\mathbb K$-inf-compactness is the published `FeinbergLiang.ACOE.KInfCompact`. The state space is nonempty and standard Borel, as in the paper's setup with an initial prior; a filter satisfying (3.3) therefore exists, so the quantified transition clause is substantive. Assumption (a) of Theorem 3.2 is stated with the discount factor $\alpha$: (D) is $0 \le \alpha < 1$, while (P) is $c \ge 0$ and $0 \le \alpha \le 1$. The paper's tail "and therefore statements (i)–(vi) of Theorem 3.1 hold" is not stated: it is Theorem 2.1 applied to the COMDP, which the paper cites from Feinberg et al. [14, Theorem 2] and does not prove.
-- source:
--   Feinberg, Kasyanov, Zgurovsky, Partially Observable Total-Cost Markov Decision Processes with Weakly Continuous Transition Probabilities, arXiv:1401.2168v2, Theorem 3.6, p. 12, with assumptions (a), (b) of Theorem 3.2, p. 11

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_FeinbergPOMDP_WStar_Model

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter FeinbergLiang.ACOE

namespace FeinbergPOMDP.WStar

/-- Feinberg, Kasyanov, Zgurovsky, arXiv:1401.2168v2, **Theorem 3.6**, its Assumption (W*)
conclusion (p. 12): if (D) or (P) holds, the POMDP cost `c` is bounded below and
`𝕂`-inf-compact on `𝕏 × 𝔸`, the transition kernel `P(dx′ | x, a)` is weakly continuous and the
observation kernel `Q(dy | a, x)` is continuous in the total variation, then the COMDP
`(ℙ(𝕏), 𝔸, q, c̄)` satisfies Assumption (W*): `c̄` is bounded below by every lower bound of `c` and
`𝕂`-inf-compact on `ℙ(𝕏) × 𝔸`, and `q(· | z, a)` is weakly continuous in `(z, a)`.

Formalization Note. `𝕏, 𝕐, 𝔸` are Borel subsets of Polish spaces (p. 4), encoded as separable metrizable spaces with
their Borel σ-algebras (`PolishSpace` is not assumed). The cost `c : 𝕏 × 𝔸 → ℝ ∪ {+∞}`, bounded below and Borel (p. 4), is written `c(x, a) = lower + f x a`
with `lower : ℝ` and `f : 𝕏 → 𝔸 → [0, ∞]` Borel; every bounded-below `ℝ ∪ {+∞}`-valued Borel
function has this form. Then `c̄(z, a) = lower + beliefCost f z a` (3.8). `𝕂`-inf-compactness is the
published `FeinbergLiang.ACOE.KInfCompact` of `f` (nonempty compact `K`, levels in `ℝ≥0`; equivalent
to the paper's definition on p. 6, since `lower + ·` shifts levels).
`q` is defined from a filter `H` satisfying (3.3); the paper notes (p. 8) that the choice of `H` does
not affect `q`, so the weak continuity is stated for every such `H`. The standard Borel and nonempty
instances on `𝕏` ensure that the paper's filtering kernel exists, so this clause is not vacuous.
Assumption (a) of Theorem 3.2 is stated explicitly: either (D), with `0 ≤ α < 1`, or
(P), with a nonnegative cost and `0 ≤ α ≤ 1`. The bounded-below part of (D) is built into
`lower + f`.
The tail "and therefore statements (i)–(vi) of Theorem 3.1 hold" is not stated: it is Theorem 2.1,
cited from Feinberg et al. [14, Theorem 2] and not proved in the paper. -/
theorem theorem_3_6 {X Y A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [TopologicalSpace.MetrizableSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    [StandardBorelSpace X] [Nonempty X]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y) [IsMarkovKernel Q]
    (lower α : ℝ) (f : X → A → ℝ≥0∞) (hf : Measurable (Function.uncurry f))
    (hDP : (0 ≤ α ∧ α < 1) ∨
      ((∀ (x : X) (a : A), (0 : EReal) ≤ (lower : EReal) + (f x a : EReal)) ∧
        0 ≤ α ∧ α ≤ 1))
    (hK : KInfCompact f)
    (hP : IsWeaklyContinuous (kernelPM P)) (hQ : IsTVContinuous (kernelPM Q)) :
    (∀ K : ℝ, (∀ (x : X) (a : A), (K : EReal) ≤ (lower : EReal) + (f x a : EReal)) →
        ∀ (z : ProbabilityMeasure X) (a : A),
          (K : EReal) ≤ (lower : EReal) + (beliefCost f z a : EReal)) ∧
    KInfCompact (beliefCost f) ∧
    ∀ H : ProbabilityMeasure X → A → Y → ProbabilityMeasure X,
      IsFilter P Q H → BeliefTransitionWeaklyContinuous P Q H := by sorry

end FeinbergPOMDP.WStar
