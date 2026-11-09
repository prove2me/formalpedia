-- Prove2me | Theorems.Thm_BourgainUnion_Euclidean_lemma_4_6
-- name    : BourgainUnion.Euclidean.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:26:47.218971+00:00
-- url     : https://prove2.me/theorems/17823f51-3e3b-4d33-a5d8-d703e38ea4ff
-- title:
--   Lemma 4.6 — eliminating one Euclidean set
-- statement:
--   Let $Y=A\sqcup B$ be a finite pseudometric space, with $A\ne\varnothing$ and $B$ Euclidean, and let $G$ be any nonnegatively weighted loopless graph on $Y$. Write $I=E_{G[B]}(d^2)$ for the internal energy and $J=\sum_{a\in A,b\in B}g_{ab}d(a,b)^2$ for the crossing energy. Then
--   $$E_{G^A}(d^2)\le E_G(d^2)+J+\sqrt{2\pi IJ}.$$
--   The conclusion includes zero energies, empty $B$, zero-distance distinct points and disconnected graphs. It bounds the cost of eliminating a single Euclidean part.
--
--   Differences from the source:
--   - encoding: real ℓ₂ and finite or infinite Euclidean target spaces → square-summable real sequences H2, with equivalent separable real Hilbert spaces where a dimension varies; reason: lp (fun _ : ℕ => ℝ) 2 is real ℓ₂; each separable real Hilbert space is isometric to a finite- or countably-dimensional ℓ₂ space
--   - encoding: a graph on a subset and a sum over unordered pairs → a weight matrix supported on that subset, with half the ordered-pair energy sum; reason: the zero diagonal and symmetry give exactly the same energy, including disconnected and all-zero graphs
--   - encoding: finite vertex sets and decompositions Y=A⊔B → a Fintype ambient type, a Finset A, and B=univ\A; reason: no vertices are identified at distance zero, and both empty B and nonempty A have the source values
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 16, Lemma 4.6, equation (9)

import Mathlib
import Definitions.Def_BourgainUnion_Euclidean_GraphModel

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean

/-- Lemma 4.6, equation (9), including zero distances and arbitrary graph weights. -/
theorem lemma_4_6 {X : Type*} [Fintype X] [DecidableEq X] [PseudoMetricSpace X]
    (A : Finset X) (hA : A.Nonempty)
    (hB : IsEuclidean ((↑(Finset.univ \ A) : Set X)))
    (G : ClusterDecomp.WGraph X) (hG : Loopless G) :
    energy (canonical G.w A) dist A ≤ energy G.w dist Finset.univ +
      crossing G.w dist A (Finset.univ \ A) +
      Real.sqrt (2*Real.pi*energy G.w dist (Finset.univ \ A)*
        crossing G.w dist A (Finset.univ \ A)) := by sorry

end BourgainUnion.Euclidean
