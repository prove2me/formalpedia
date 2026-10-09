-- Prove2me | Theorems.Thm_FeinbergPOMDP_WStar_theorem_3_4
-- name    : FeinbergPOMDP.WStar.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:55:46.029029+00:00
-- url     : https://prove2.me/theorems/a7961cf9-0f26-4d34-961f-33689f790006
-- title:
--   Theorem 3.4 — the COMDP cost c̄ is bounded below by the same constant and 𝕂-inf-compact on ℙ(𝕏) × 𝔸
-- statement:
--   Let $\mathbb X$ and $\mathbb A$ be Borel subsets of Polish spaces and give $\mathbb P(\mathbb X)$ the topology of weak convergence. A function $g$ on $\mathbb S_1 \times \mathbb S_2$ with values in $\mathbb R \cup \{+\infty\}$ is **$\mathbb K$-inf-compact** if for every compact $K \subseteq \mathbb S_1$ and every real $\lambda$ the set $\{(s_1, s_2) : s_1 \in K,\ g(s_1, s_2) \le \lambda\}$ is compact.
--
--   Let $c : \mathbb X \times \mathbb A \to \mathbb R \cup \{+\infty\}$ be Borel, bounded below and $\mathbb K$-inf-compact on $\mathbb X \times \mathbb A$. Then the belief cost
--   $$\bar c(z, a) = \int_{\mathbb X} c(x, a)\,z(dx)$$
--   satisfies $\bar c \ge K$ on $\mathbb P(\mathbb X) \times \mathbb A$ for every real $K$ with $c \ge K$ on $\mathbb X \times \mathbb A$, and $\bar c$ is $\mathbb K$-inf-compact on $\mathbb P(\mathbb X) \times \mathbb A$ (with compact sets of $\mathbb P(\mathbb X)$ taken in the weak topology).
--
--   This is part (i) of Assumption (W*) for the belief MDP, the cost half of Theorem 3.6.
--
--   **Formalization Note.** The cost is written $c = \ell + f$ with $\ell \in \mathbb R$ and $f$ Borel with values in $[0, \infty]$; $\bar c = \ell + \int f(\cdot, a)\,dz$. $\mathbb K$-inf-compactness is the published `FeinbergLiang.ACOE.KInfCompact` applied to $f$ and to $(z, a) \mapsto \int f(\cdot, a)\,dz$; it quantifies over nonempty compact sets and levels $\lambda \ge 0$ of $f$, which is equivalent to the definition above for $c$. The lower bound is compared in the extended reals.
-- source:
--   Feinberg, Kasyanov, Zgurovsky, Partially Observable Total-Cost Markov Decision Processes with Weakly Continuous Transition Probabilities, arXiv:1401.2168v2, Theorem 3.4, p. 12 (proof p. 24)

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_FeinbergPOMDP_WStar_Model

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter FeinbergLiang.ACOE

namespace FeinbergPOMDP.WStar

/-- Feinberg, Kasyanov, Zgurovsky, arXiv:1401.2168v2, **Theorem 3.4** (p. 12; proof p. 24): if `c : 𝕏 × 𝔸 → ℝ̄` is bounded below and
`𝕂`-inf-compact on `𝕏 × 𝔸`, then the COMDP cost `c̄` of (3.8) is bounded from below by the same
constant as `c` and `𝕂`-inf-compact on `ℙ(𝕏) × 𝔸` (compact sets of `ℙ(𝕏)` in the weak topology).

Formalization Note. `𝕏, 𝕐, 𝔸` are Borel subsets of Polish spaces (p. 4), encoded as separable metrizable spaces with
their Borel σ-algebras (`PolishSpace` is not assumed). The cost `c : 𝕏 × 𝔸 → ℝ ∪ {+∞}`, bounded below and Borel (p. 4), is written `c(x, a) = lower + f x a`
with `lower : ℝ` and `f : 𝕏 → 𝔸 → [0, ∞]` Borel; every bounded-below `ℝ ∪ {+∞}`-valued Borel
function has this form. Then `c̄(z, a) = lower + beliefCost f z a` (3.8). `𝕂`-inf-compactness is the
published `FeinbergLiang.ACOE.KInfCompact` of `f` (nonempty compact `K`, levels in `ℝ≥0`; equivalent
to the paper's definition on p. 6, since `lower + ·` shifts levels). "Bounded from below by the same constant" is stated
for every real lower bound `K` of `c`, in `EReal`. -/
theorem theorem_3_4 {X A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    (lower : ℝ) (f : X → A → ℝ≥0∞) (hf : Measurable (Function.uncurry f))
    (hK : KInfCompact f) :
    (∀ K : ℝ, (∀ (x : X) (a : A), (K : EReal) ≤ (lower : EReal) + (f x a : EReal)) →
        ∀ (z : ProbabilityMeasure X) (a : A),
          (K : EReal) ≤ (lower : EReal) + (beliefCost f z a : EReal)) ∧
    KInfCompact (beliefCost f) := by sorry

end FeinbergPOMDP.WStar
