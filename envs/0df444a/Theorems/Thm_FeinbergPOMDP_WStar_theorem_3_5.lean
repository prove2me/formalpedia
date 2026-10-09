-- Prove2me | Theorems.Thm_FeinbergPOMDP_WStar_theorem_3_5
-- name    : FeinbergPOMDP.WStar.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:56:01.485277+00:00
-- url     : https://prove2.me/theorems/3555400a-63e1-457d-a7f1-61a9480d3907
-- title:
--   Theorem 3.5 — condition (c) of Theorem 3.2 makes the belief transition q(dz′|z, a) weakly continuous
-- statement:
--   Let $\mathbb X, \mathbb Y, \mathbb A$ be Borel subsets of Polish spaces, with POMDP kernels $P(dx' \mid x, a)$ and $Q(dy \mid a, x)$, and let $q(dz' \mid z, a)$ be the belief transition (3.5) of the COMDP. Suppose condition (c) of Theorem 3.2 holds, i.e. either
--
--   1. the observation kernel $R'(dy \mid z, a)$ on $\mathbb Y$ given $\mathbb P(\mathbb X) \times \mathbb A$ is setwise continuous and Assumption (H) holds, or
--   2. $P$ and $Q$ are weakly continuous and there is a weakly continuous stochastic kernel $H(dx \mid z, a, y)$ on $\mathbb X$ given $\mathbb P(\mathbb X) \times \mathbb A \times \mathbb Y$ satisfying (3.3).
--
--   Then $q$ is weakly continuous: for every filter $H$ satisfying (3.3), whenever $z^{(n)} \to z$ weakly and $a^{(n)} \to a$,
--   $$\int_{\mathbb P(\mathbb X)} g\,dq(\cdot \mid z^{(n)}, a^{(n)}) \to \int_{\mathbb P(\mathbb X)} g\,dq(\cdot \mid z, a)\quad\text{for every bounded continuous } g : \mathbb P(\mathbb X) \to \mathbb R .$$
--
--   This is part (ii) of Assumption (W*) for the belief MDP, derived from properties of $R'$ and of the filter.
--
--   **Formalization Note.** The paper notes (p. 8) that the choice of the filter does not affect $q$, so the conclusion is stated for every filter satisfying (3.3); the filter in alternative 2 is one particular one. Weak continuity of kernels is the sequential definition of p. 4.
-- source:
--   Feinberg, Kasyanov, Zgurovsky, Partially Observable Total-Cost Markov Decision Processes with Weakly Continuous Transition Probabilities, arXiv:1401.2168v2, Theorem 3.5, p. 12 (proof p. 17), with condition (c) of Theorem 3.2, p. 11

import Mathlib
import Definitions.Def_FeinbergPOMDP_WStar_Model

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter

namespace FeinbergPOMDP.WStar

/-- Feinberg, Kasyanov, Zgurovsky, arXiv:1401.2168v2, **Theorem 3.5** (p. 12; proof p. 17): the stochastic kernel `q(dz′ | z, a)` on
`ℙ(𝕏)` given `ℙ(𝕏) × 𝔸` is weakly continuous if condition (c) of Theorem 3.2 (p. 11) holds:
either (i) `R′(dy | z, a)` is setwise continuous and Assumption (H) holds, or (ii) `P` and `Q` are
weakly continuous and there is a weakly continuous stochastic kernel `H(dx | z, a, y)` on `𝕏` given
`ℙ(𝕏) × 𝔸 × 𝕐` satisfying (3.3).

Formalization Note. `𝕏, 𝕐, 𝔸` are Borel subsets of Polish spaces (p. 4), encoded as separable metrizable spaces with
their Borel σ-algebras (`PolishSpace` is not assumed). `q` is defined from a filter `H` satisfying (3.3), and the paper
notes (p. 8) that its choice does not affect `q`; the conclusion is therefore stated for every such
`H`, while the `H` of condition (c)(ii) is one particular filter. Weak continuity of kernels is
the sequential definition of p. 4 (`IsWeaklyContinuous`). -/
theorem theorem_3_5 {X Y A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [TopologicalSpace.MetrizableSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y) [IsMarkovKernel Q]
    (hc : (IsSetwiseContinuous (fun p : ProbabilityMeasure X × A => obsLaw P Q p.1 p.2) ∧
            AssumptionH P Q) ∨
          (IsWeaklyContinuous (kernelPM P) ∧ IsWeaklyContinuous (kernelPM Q) ∧
            ∃ H₀ : ProbabilityMeasure X → A → Y → ProbabilityMeasure X, IsFilter P Q H₀ ∧
              IsWeaklyContinuous (fun p : ProbabilityMeasure X × A × Y => H₀ p.1 p.2.1 p.2.2)))
    (H : ProbabilityMeasure X → A → Y → ProbabilityMeasure X) (hH : IsFilter P Q H) :
    BeliefTransitionWeaklyContinuous P Q H := by sorry

end FeinbergPOMDP.WStar
