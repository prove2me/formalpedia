-- Prove2me | Theorems.Thm_BourgainUnion_Euclidean_lemma_4_9
-- name    : BourgainUnion.Euclidean.lemma_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:27:10.787585+00:00
-- url     : https://prove2.me/theorems/bc9ff8e5-f931-4483-9c95-d136197d1ece
-- title:
--   Lemma 4.9 — one-point Euclidean energy bound
-- statement:
--   In the setting of Lemma 4.6, assume additionally that $B\cup\{a\}$ is Euclidean for every $a\in A$. With $I$ and $J$ the internal and crossing energies of $B$, respectively,
--   $$E_{G^A}(d^2)\le E_{G[A]}(d^2)+\frac12\left(\sqrt J+\sqrt{J+I+\sqrt{I(I+J)}}\right)^2.$$
--   All graph weights may vanish and $B$ may be empty. The nested radicals and the induced energy on $A$ are retained literally. This sharper one-point estimate supports the second branch of Lemma 1.5 and the 3.86 bound in Theorem B.2.
--
--   Differences from the source:
--   - encoding: real ℓ₂ and finite or infinite Euclidean target spaces → square-summable real sequences H2, with equivalent separable real Hilbert spaces where a dimension varies; reason: lp (fun _ : ℕ => ℝ) 2 is real ℓ₂; each separable real Hilbert space is isometric to a finite- or countably-dimensional ℓ₂ space
--   - encoding: a graph on a subset and a sum over unordered pairs → a weight matrix supported on that subset, with half the ordered-pair energy sum; reason: the zero diagonal and symmetry give exactly the same energy, including disconnected and all-zero graphs
--   - encoding: finite vertex sets and decompositions Y=A⊔B → a Fintype ambient type, a Finset A, and B=univ\A; reason: no vertices are identified at distance zero, and both empty B and nonempty A have the source values
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 20, Lemma 4.9, equation (17)

import Mathlib
import Definitions.Def_BourgainUnion_Euclidean_GraphModel

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean

/-- Lemma 4.9, equation (17); the subtraction-free nested radical is literal. -/
theorem lemma_4_9 {X : Type*} [Fintype X] [DecidableEq X] [PseudoMetricSpace X]
    (A : Finset X) (hA : A.Nonempty)
    (hB : IsEuclidean (↑(Finset.univ \ A) : Set X))
    (hone : ∀ a ∈ A, IsEuclidean ((↑(Finset.univ \ A) : Set X) ∪ {a}))
    (G : ClusterDecomp.WGraph X) (hG : Loopless G) :
    let I := energy G.w dist (Finset.univ \ A)
    let J := crossing G.w dist A (Finset.univ \ A)
    energy (canonical G.w A) dist A ≤ energy G.w dist A +
      (1/2) * (Real.sqrt J + Real.sqrt (J+I+Real.sqrt (I*(I+J))))^2 := by sorry

end BourgainUnion.Euclidean
