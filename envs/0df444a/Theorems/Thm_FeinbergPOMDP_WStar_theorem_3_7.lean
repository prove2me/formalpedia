-- Prove2me | Theorems.Thm_FeinbergPOMDP_WStar_theorem_3_7
-- name    : FeinbergPOMDP.WStar.theorem_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:56:07.804868+00:00
-- url     : https://prove2.me/theorems/7bcc0ff6-0c45-4814-b0fa-40b1537ef266
-- title:
--   Theorem 3.7 — weakly continuous P and total-variation-continuous Q give setwise continuous R′, Assumption (H), and weakly continuous q
-- statement:
--   Let $\mathbb X, \mathbb Y, \mathbb A$ be Borel subsets of Polish spaces, let the transition kernel $P(dx' \mid x, a)$ be weakly continuous, and let the observation kernel $Q(dy \mid a, x)$ be continuous in the total variation. Then
--
--   1. the observation kernel $R'(dy \mid z, a)$ of (3.2) is setwise continuous on $\mathbb P(\mathbb X) \times \mathbb A$;
--   2. Assumption (H) holds;
--   3. therefore the belief transition $q(dz' \mid z, a)$ of (3.5) is weakly continuous on $\mathbb P(\mathbb X) \times \mathbb A$ (for every filter $H$ satisfying (3.3)).
--
--   Together with Theorem 3.4 this gives Theorem 3.6.
--
--   **Formalization Note.** $\mathbb X$ is moreover standard Borel and nonempty, as in the paper's POMDP setup with an initial prior. Assumption (H) asserts that a filter exists, which the paper obtains from Bertsekas and Shreve [8, Proposition 7.27] for such spaces.
-- source:
--   Feinberg, Kasyanov, Zgurovsky, Partially Observable Total-Cost Markov Decision Processes with Weakly Continuous Transition Probabilities, arXiv:1401.2168v2, Theorem 3.7, p. 12 (proof p. 22)

import Mathlib
import Definitions.Def_FeinbergPOMDP_WStar_Model

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter

namespace FeinbergPOMDP.WStar

/-- Feinberg, Kasyanov, Zgurovsky, arXiv:1401.2168v2, **Theorem 3.7** (p. 12; proof p. 22): weak continuity of `P(dx′ | x, a)` and
continuity in the total variation of `Q(dy | a, x)` imply condition (c)(i) of Theorem 3.2 (`R′` is
setwise continuous and Assumption (H) holds), and therefore `q(dz′ | z, a)` is weakly continuous.

Formalization Note. `𝕏, 𝕐, 𝔸` are Borel subsets of Polish spaces (p. 4), encoded as separable metrizable spaces with
their Borel σ-algebras (`PolishSpace` is not assumed). `𝕏` is moreover standard Borel, as every Borel subset of a Polish
space is: Assumption (H) asserts the existence of a filter `H`, which the paper takes from
Bertsekas–Shreve [8, Prop. 7.27] for such spaces. Weak continuity of `q` is stated for every filter
`H` satisfying (3.3) (its choice does not affect `q`, p. 8). -/
theorem theorem_3_7 {X Y A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [TopologicalSpace.MetrizableSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    [StandardBorelSpace X] [Nonempty X]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y) [IsMarkovKernel Q]
    (hP : IsWeaklyContinuous (kernelPM P)) (hQ : IsTVContinuous (kernelPM Q)) :
    IsSetwiseContinuous (fun p : ProbabilityMeasure X × A => obsLaw P Q p.1 p.2) ∧
    AssumptionH P Q ∧
    ∀ H : ProbabilityMeasure X → A → Y → ProbabilityMeasure X,
      IsFilter P Q H → BeliefTransitionWeaklyContinuous P Q H := by sorry

end FeinbergPOMDP.WStar
