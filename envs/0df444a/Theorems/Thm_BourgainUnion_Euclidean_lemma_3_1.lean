-- Prove2me | Theorems.Thm_BourgainUnion_Euclidean_lemma_3_1
-- name    : BourgainUnion.Euclidean.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:25:43.307439+00:00
-- url     : https://prove2.me/theorems/e2a94509-e124-472a-8144-b1afa5c28688
-- title:
--   Lemma 3.1 — extension to terminal embedding
-- statement:
--   Let $V$ be a nonempty subset of a finite metric space $X$ and let $D\ge1$. Suppose a map $\phi:V\to\ell_2$ does not contract any distance on $V$ and has an extension $\widetilde\phi:X\to\ell_2$ of Lipschitz constant at most $D$. Then there is a globally $1$-Lipschitz map $g:X\to\ell_2$ satisfying
--   $$\|g(u)-g(x)\|\ge\frac{d(u,x)}{3\sqrt2\,D}\qquad(u\in V,\ x\in X).$$
--   Thus $V$ has a $3\sqrt2\,D$-terminal embedding. The prescribed map need not be an isometry. This connects extension bounds to the terminal-combination theorem.
--
--   Differences from the source:
--   - encoding: real ℓ₂ and finite or infinite Euclidean target spaces → square-summable real sequences H2, with equivalent separable real Hilbert spaces where a dimension varies; reason: lp (fun _ : ℕ => ℝ) 2 is real ℓ₂; each separable real Hilbert space is isometric to a finite- or countably-dimensional ℓ₂ space
--   - encoding: maps defined only on a specified subset → total representatives on the ambient type, constrained only on that subset; reason: every subset map has a total representative by setting it to zero off the subset; those extra values impose no conditions
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 11, Lemma 3.1

import Mathlib
import Definitions.Def_BourgainUnion_Euclidean_EmbeddingModel

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean

/-- Lemma 3.1: factor 3 sqrt(2) D, with no isometry requirement on the prescribed map. -/
theorem lemma_3_1 {X : Type*} [MetricSpace X] [Fintype X]
    (V : Set X) (hV : V.Nonempty) (D : ℝ) (hD : 1 ≤ D)
    (φ F : X → H2)
    (hnoncontract : ∀ x ∈ V, ∀ y ∈ V, dist x y ≤ dist (φ x) (φ y))
    (hextend : Set.EqOn F φ V) (hF : LipOn D F Set.univ) :
    ∃ g : X → H2, Terminal V (3*Real.sqrt 2*D) g := by sorry

end BourgainUnion.Euclidean
