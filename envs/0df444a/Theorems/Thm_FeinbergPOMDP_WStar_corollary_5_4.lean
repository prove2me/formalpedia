-- Prove2me | Theorems.Thm_FeinbergPOMDP_WStar_corollary_5_4
-- name    : FeinbergPOMDP.WStar.corollary_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:55:42.725681+00:00
-- url     : https://prove2.me/theorems/976a743e-d187-4f72-9bc2-d17a7fa6d38f
-- title:
--   Corollary 5.4 — the observation kernel R′(dy|z, a) is continuous in the total variation
-- statement:
--   Let $\mathbb X, \mathbb Y, \mathbb A$ be Borel subsets of Polish spaces, let $P(dx' \mid x, a)$ be weakly continuous and $Q(dy \mid a, x)$ continuous in the total variation. Then the observation kernel
--   $$R'(C \mid z, a) = \int_{\mathbb X}\int_{\mathbb X} Q(C \mid a, x')\,P(dx' \mid x, a)\,z(dx)$$
--   of (3.2) on $\mathbb Y$ given $\mathbb P(\mathbb X) \times \mathbb A$ is continuous in the total variation: $R'(\cdot \mid z^{(n)}, a^{(n)}) \to R'(\cdot \mid z, a)$ in the total variation whenever $z^{(n)} \to z$ weakly and $a^{(n)} \to a$.
--
--   In particular $R'$ is setwise continuous, which is the first half of condition (c)(i) of Theorem 3.2.
--
--   **Formalization Note.** Total variation is in the function form of p. 4 (supremum over Borel $f$ with values in $[-1, 1]$), the same predicate as the hypothesis on $Q$.
-- source:
--   Feinberg, Kasyanov, Zgurovsky, Partially Observable Total-Cost Markov Decision Processes with Weakly Continuous Transition Probabilities, arXiv:1401.2168v2, Corollary 5.4, p. 20

import Mathlib
import Definitions.Def_FeinbergPOMDP_WStar_Model

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter

namespace FeinbergPOMDP.WStar

/-- Feinberg, Kasyanov, Zgurovsky, arXiv:1401.2168v2, **Corollary 5.4** (p. 20): under the assumptions of Lemma 5.3 (`P` weakly
continuous, `Q` continuous in the total variation), the observation kernel `R′(dy | z, a)` of (3.2)
on `𝕐` given `ℙ(𝕏) × 𝔸` is continuous in the total variation.

Formalization Note. `𝕏, 𝕐, 𝔸` are Borel subsets of Polish spaces (p. 4), encoded as separable metrizable spaces with
their Borel σ-algebras (`PolishSpace` is not assumed). Total variation is in the function form of p. 4 (`IsTVContinuous`),
the same predicate as the hypothesis on `Q`. -/
theorem corollary_5_4 {X Y A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [TopologicalSpace.MetrizableSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y) [IsMarkovKernel Q]
    (hP : IsWeaklyContinuous (kernelPM P)) (hQ : IsTVContinuous (kernelPM Q)) :
    IsTVContinuous (fun p : ProbabilityMeasure X × A => obsLaw P Q p.1 p.2) := by sorry

end FeinbergPOMDP.WStar
