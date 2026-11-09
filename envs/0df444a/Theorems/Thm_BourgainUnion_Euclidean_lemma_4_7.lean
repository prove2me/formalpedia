-- Prove2me | Theorems.Thm_BourgainUnion_Euclidean_lemma_4_7
-- name    : BourgainUnion.Euclidean.lemma_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:27:03.814931+00:00
-- url     : https://prove2.me/theorems/8816e482-805a-4837-a68f-1e121690b059
-- title:
--   Lemma 4.7 — energy bounds give pairwise extensions
-- statement:
--   Let $Y=A\sqcup B$ be a finite pseudometric space with $A\ne\varnothing$, and let $t,s\ge1$. Suppose every graph $G$ with nonnegative weights and no edges within $A$ satisfies
--   $$E_{G^A}(d^2)\le t^2I+s^2J,$$
--   where $I$ and $J$ are the internal and crossing energies defined in Lemma 4.6. Every $1$-Lipschitz map $f:A\to\ell_2$ then has an extension $F:Y\to\ell_2$ satisfying
--   $$\|F(b)-F(b')\|\le td(b,b'),\qquad \|F(a)-F(b)\|\le sd(a,b)$$
--   for all $a\in A$, $b,b'\in B$, and
--   $$F(Y)\subseteq\operatorname{conv}(f(A)).$$
--   This transfers a universally weighted energy inequality to simultaneous pairwise extension bounds, preserving both coefficients and the convex-hull conclusion.
--
--   Differences from the source:
--   - encoding: real ℓ₂ and finite or infinite Euclidean target spaces → square-summable real sequences H2, with equivalent separable real Hilbert spaces where a dimension varies; reason: lp (fun _ : ℕ => ℝ) 2 is real ℓ₂; each separable real Hilbert space is isometric to a finite- or countably-dimensional ℓ₂ space
--   - encoding: maps defined only on a specified subset → total representatives on the ambient type, constrained only on that subset; reason: every subset map has a total representative by setting it to zero off the subset; those extra values impose no conditions
--   - encoding: a graph on a subset and a sum over unordered pairs → a weight matrix supported on that subset, with half the ordered-pair energy sum; reason: the zero diagonal and symmetry give exactly the same energy, including disconnected and all-zero graphs
--   - encoding: finite vertex sets and decompositions Y=A⊔B → a Fintype ambient type, a Finset A, and B=univ\A; reason: no vertices are identified at distance zero, and both empty B and nonempty A have the source values
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 19, Lemma 4.7

import Mathlib
import Definitions.Def_BourgainUnion_Euclidean_GraphModel
import Definitions.Def_BourgainUnion_Euclidean_AveragingModel

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean

/-- Lemma 4.7: universally weighted energy premise, both pair bounds and convex-hull values. -/
theorem lemma_4_7 {X : Type*} [Fintype X] [DecidableEq X] [PseudoMetricSpace X]
    (A : Finset X) (hA : A.Nonempty) (t s : ℝ) (ht : 1 ≤ t) (hs : 1 ≤ s)
    (henergy : ∀ G : ClusterDecomp.WGraph X, Loopless G →
      (∀ a ∈ A, ∀ a' ∈ A, G.w a a' = 0) →
      energy (canonical G.w A) dist A ≤ t^2 * energy G.w dist (Finset.univ \ A) +
        s^2 * crossing G.w dist A (Finset.univ \ A))
    (f : X → H2) (hf : LipOn 1 f (A : Set X)) :
    ∃ F : X → H2,
      PairwiseExtension t s Set.univ (↑(Finset.univ \ A) : Set X) f F := by sorry

end BourgainUnion.Euclidean
