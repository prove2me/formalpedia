-- Prove2me | Theorems.Thm_FeinbergPOMDP_WStar_lemma_5_3
-- name    : FeinbergPOMDP.WStar.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:55:48.812211+00:00
-- url     : https://prove2.me/theorems/ff1030f1-e293-4936-838e-1a09c2721c06
-- title:
--   Lemma 5.3 — 𝓡_{𝒪₁∖𝒪₂} is uniformly bounded and equicontinuous, uniformly over observation sets C
-- statement:
--   Let $\mathbb X, \mathbb Y, \mathbb A$ be Borel subsets of Polish spaces, let the transition kernel $P(dx' \mid x, a)$ be weakly continuous and the observation kernel $Q(dy \mid a, x)$ be continuous in the total variation, and let $R(\cdot \mid z, a)$ be the joint law of the next state and observation (3.1). Then for every pair of open sets $\mathcal O_1, \mathcal O_2 \subseteq \mathbb X$ the family
--   $$\mathcal R_{\mathcal O_1 \setminus \mathcal O_2} = \big\{(z, a) \mapsto R((\mathcal O_1 \setminus \mathcal O_2) \times C \mid z, a) : C \subseteq \mathbb Y \text{ Borel}\big\}$$
--   is bounded by $1$ and equicontinuous at every point of $\mathbb P(\mathbb X) \times \mathbb A$: whenever $z^{(n)} \to z$ weakly and $a^{(n)} \to a$,
--   $$\sup_{C \in \mathcal B(\mathbb Y)} \big|R((\mathcal O_1 \setminus \mathcal O_2) \times C \mid z^{(n)}, a^{(n)}) - R((\mathcal O_1 \setminus \mathcal O_2) \times C \mid z, a)\big| \to 0. \tag{5.15}$$
--
--   The convergence is uniform in $C$; it gives the total-variation continuity of $R'$ (Corollary 5.4) and the hypothesis of Lemma 5.6.
--
--   **Formalization Note.** The supremum over $C$ is written in $\varepsilon$–$N$ form: for every $\varepsilon > 0$ there is $N$ with the difference at most $\varepsilon$ for all $n \ge N$ and all Borel $C$.
-- source:
--   Feinberg, Kasyanov, Zgurovsky, Partially Observable Total-Cost Markov Decision Processes with Weakly Continuous Transition Probabilities, arXiv:1401.2168v2, Lemma 5.3 and (5.14), (5.15), p. 19

import Mathlib
import Definitions.Def_FeinbergPOMDP_WStar_Model

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter

namespace FeinbergPOMDP.WStar

/-- Feinberg, Kasyanov, Zgurovsky, arXiv:1401.2168v2, **Lemma 5.3** (p. 19): if `P(dx′ | x, a)` is weakly continuous and `Q(dy | a, x)`
is continuous in the total variation, then for every pair of open sets `𝒪₁, 𝒪₂ ⊆ 𝕏` the family
`𝓡_{𝒪₁ ∖ 𝒪₂} = {(z, a) ↦ R((𝒪₁ ∖ 𝒪₂) × C | z, a) : C ∈ ℬ(𝕐)}` (5.14) is uniformly bounded and
equicontinuous at all points of `ℙ(𝕏) × 𝔸`, i.e. (5.15): whenever `z⁽ⁿ⁾ → z` weakly and `a⁽ⁿ⁾ → a`,
`sup_{C ∈ ℬ(𝕐)} |R((𝒪₁ ∖ 𝒪₂) × C | z⁽ⁿ⁾, a⁽ⁿ⁾) − R((𝒪₁ ∖ 𝒪₂) × C | z, a)| → 0`.

Formalization Note. `𝕏, 𝕐, 𝔸` are Borel subsets of Polish spaces (p. 4), encoded as separable metrizable spaces with
their Borel σ-algebras (`PolishSpace` is not assumed). `R` is `jointLaw` (3.1). The uniform bound is `1`, the bound
the paper's proof gives. The convergence (5.15) is uniform over all Borel `C` (`REquicontinuous`). -/
theorem lemma_5_3 {X Y A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [TopologicalSpace.MetrizableSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y) [IsMarkovKernel Q]
    (hP : IsWeaklyContinuous (kernelPM P)) (hQ : IsTVContinuous (kernelPM Q))
    (O₁ O₂ : Set X) (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂) :
    (∀ (C : {C : Set Y // MeasurableSet C}) (p : ProbabilityMeasure X × A),
        |RFamily P Q (O₁ \ O₂) C p| ≤ 1) ∧
    REquicontinuous P Q (O₁ \ O₂) := by sorry

end FeinbergPOMDP.WStar
