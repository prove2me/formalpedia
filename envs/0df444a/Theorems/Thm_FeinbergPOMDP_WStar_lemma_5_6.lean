-- Prove2me | Theorems.Thm_FeinbergPOMDP_WStar_lemma_5_6
-- name    : FeinbergPOMDP.WStar.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:56:01.414291+00:00
-- url     : https://prove2.me/theorems/adc95ce7-2c99-4f67-9b0f-5fa315895903
-- title:
--   Lemma 5.6 — equicontinuity of 𝓡_𝒪 on finite intersections of a countable base implies (5.21) and Assumption (H)
-- statement:
--   Let $\mathbb X, \mathbb Y, \mathbb A$ be Borel subsets of Polish spaces, with POMDP kernels $P$, $Q$ and the kernels $R$, $R'$ of (3.1)–(3.2). Suppose the topology of $\mathbb X$ has a countable base $\tau_b = \{\mathcal O^{(j)}\}_{j \ge 1}$ such that for every finite intersection $\mathcal O = \bigcap_{i=1}^N \mathcal O^{(j_i)}$ ($N \ge 1$) of its elements, the family $\mathcal R_{\mathcal O} = \{(z, a) \mapsto R(\mathcal O \times C \mid z, a) : C \in \mathcal B(\mathbb Y)\}$ is equicontinuous at every point of $\mathbb P(\mathbb X) \times \mathbb A$ in the sense of (5.15). Let $H$ be any filter satisfying (3.3).
--
--   Then for any sequences $z^{(n)} \to z$ weakly in $\mathbb P(\mathbb X)$ and $a^{(n)} \to a$ in $\mathbb A$ there are a subsequence $(z^{(n_k)}, a^{(n_k)})$ and a Borel set $C^* \subseteq \mathbb Y$ such that
--   $$R'(C^* \mid z, a) = 1 \quad\text{and}\quad H(\cdot \mid z^{(n_k)}, a^{(n_k)}, y) \to H(\cdot \mid z, a, y) \text{ weakly for all } y \in C^*, \tag{5.21}$$
--   and therefore Assumption (H) holds.
--
--   This is the step that produces Assumption (H) in Theorem 3.7.
--
--   **Formalization Note.** The base is a sequence $\mathcal O^{(j)}$ whose range is a topological basis; finite intersections are over nonempty finite index sets. Equicontinuity of $\mathcal R_{\mathcal O}$ is the sequential form (5.15), uniform over Borel $C$. The lemma assumes nothing on $P$ and $Q$ beyond the standing setup.
-- source:
--   Feinberg, Kasyanov, Zgurovsky, Partially Observable Total-Cost Markov Decision Processes with Weakly Continuous Transition Probabilities, arXiv:1401.2168v2, Lemma 5.6, p. 21

import Mathlib
import Definitions.Def_FeinbergPOMDP_WStar_Model

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter

namespace FeinbergPOMDP.WStar

/-- Feinberg, Kasyanov, Zgurovsky, arXiv:1401.2168v2, **Lemma 5.6** (p. 21): if the topology of `𝕏` has a countable base
`τ_b = {𝒪⁽ʲ⁾}_{j ≥ 1}` such that for every finite intersection `𝒪 = ⋂_{i=1}^N 𝒪⁽ʲⁱ⁾` of its elements
the family `𝓡_𝒪` of (5.14) is equicontinuous at all points of `ℙ(𝕏) × 𝔸`, then for any `z⁽ⁿ⁾ → z`
weakly and `a⁽ⁿ⁾ → a` there are a subsequence `(z⁽ⁿᵏ⁾, a⁽ⁿᵏ⁾)` and `C* ∈ ℬ(𝕐)` with `R′(C* | z, a) = 1`
and `H(· | z⁽ⁿᵏ⁾, a⁽ⁿᵏ⁾, y) → H(· | z, a, y)` weakly for all `y ∈ C*` (5.21); therefore Assumption (H)
holds.

Formalization Note. `𝕏, 𝕐, 𝔸` are Borel subsets of Polish spaces (p. 4), encoded as separable metrizable spaces with
their Borel σ-algebras (`PolishSpace` is not assumed). The base is `O : ℕ → Set 𝕏` with `Set.range O` a topological
basis; finite intersections are over nonempty finite index sets (`N ≥ 1`). Equicontinuity of `𝓡_𝒪`
is the sequential, uniform-in-`C` form (5.15) (`REquicontinuous`). `H` is any filter satisfying (3.3)
(`IsFilter`); (5.21) is concluded for that `H`, and then Assumption (H). The lemma assumes nothing
on `P` and `Q` beyond the standing ones. -/
theorem lemma_5_6 {X Y A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [TopologicalSpace.MetrizableSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y) [IsMarkovKernel Q]
    (O : ℕ → Set X) (hO : TopologicalSpace.IsTopologicalBasis (Set.range O))
    (hR : ∀ s : Finset ℕ, s.Nonempty → REquicontinuous P Q (⋂ j ∈ s, O j))
    (H : ProbabilityMeasure X → A → Y → ProbabilityMeasure X) (hH : IsFilter P Q H) :
    (∀ (z : ProbabilityMeasure X) (a : A) (zs : ℕ → ProbabilityMeasure X) (as : ℕ → A),
      Tendsto zs atTop (𝓝 z) → Tendsto as atTop (𝓝 a) →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ C : Set Y, MeasurableSet C ∧
          (obsLaw P Q z a : Measure Y) C = 1 ∧
          ∀ y ∈ C, Tendsto (fun k => H (zs (φ k)) (as (φ k)) y) atTop (𝓝 (H z a y))) ∧
    AssumptionH P Q := by sorry

end FeinbergPOMDP.WStar
