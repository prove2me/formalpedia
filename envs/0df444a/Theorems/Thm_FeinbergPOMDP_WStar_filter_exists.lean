-- Prove2me | Theorems.Thm_FeinbergPOMDP_WStar_filter_exists
-- name    : FeinbergPOMDP.WStar.filter_exists
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-04T17:54:49.068424+00:00
-- url     : https://prove2.me/theorems/a2d63d04-68d6-4b86-a39a-148a68fbc827
-- title:
--   Existence of a filter $H$ satisfying (3.3) (Bertsekas–Shreve Prop. 7.27)
-- statement:
--   Let $\mathbb X,\mathbb Y,\mathbb A$ be separable metrizable spaces with their Borel $\sigma$-algebras, with $\mathbb X$ nonempty and standard Borel, and let $P(dx'\mid x,a)$ and $Q(dy\mid a,x)$ be stochastic kernels on $\mathbb X$ given $\mathbb X\times\mathbb A$ and on $\mathbb Y$ given $\mathbb A\times\mathbb X$. Let $R(\cdot\mid z,a)$ be the joint law (3.1) of $(x',y)$ and $R'(\cdot\mid z,a)$ its $\mathbb Y$-marginal (3.2).
--
--   Then there exists a stochastic kernel $H(dx\mid z,a,y)$ on $\mathbb X$ given $\mathbb P(\mathbb X)\times\mathbb A\times\mathbb Y$ satisfying (3.3):
--   $$R(B\times C\mid z,a)=\int_C H(B\mid z,a,y)\,R'(dy\mid z,a),\qquad B\in\mathcal B(\mathbb X),\ C\in\mathcal B(\mathbb Y),\ z\in\mathbb P(\mathbb X),\ a\in\mathbb A .$$
--   Here "stochastic kernel" is encoded by `IsFilter`: $y\mapsto H(z,a,y)$ is measurable for the evaluation $\sigma$-algebra on $\mathbb P(\mathbb X)$, and $(z,a,y)\mapsto H(z,a,y)$ is measurable for the Borel $\sigma$-algebras of the weak topology on $\mathbb P(\mathbb X)$ (domain and codomain).
--
--   This is the existence statement the paper invokes on p. 8 (citing Bertsekas and Shreve, Proposition 7.27) to define the belief transition $q$ in (3.5); it is the source of the filter required by Assumption (H).
-- source:
--   Feinberg, Kasyanov, Zgurovsky, Partially Observable Total-Cost Markov Decision Processes with Weakly Continuous Transition Probabilities, arXiv:1401.2168v2, p. 8, sentence preceding (3.3) (citing Bertsekas and Shreve, Stochastic Optimal Control: The Discrete-Time Case, Proposition 7.27)

import Mathlib
import Definitions.Def_FeinbergPOMDP_WStar_Model

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter

namespace FeinbergPOMDP.WStar

/-- Feinberg, Kasyanov, Zgurovsky, arXiv:1401.2168v2, p. 8, the sentence before (3.3): by Bertsekas and Shreve
[8, Proposition 7.27] there exists a stochastic kernel `H` on `𝕏` given `ℙ(𝕏) × 𝔸 × 𝕐` satisfying (3.3),
i.e. a filter in the sense of `IsFilter` (measurable posterior map, jointly Borel in `(z, a, y)`). -/
theorem filter_exists {X Y A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [TopologicalSpace.MetrizableSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    [StandardBorelSpace X] [Nonempty X]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y) [IsMarkovKernel Q] :
    ∃ H : ProbabilityMeasure X → A → Y → ProbabilityMeasure X, IsFilter P Q H := by sorry

end FeinbergPOMDP.WStar
