-- Prove2me | Theorems.Thm_FamousTheorems_exists_hilbert_basis
-- name    : FamousTheorems.exists_hilbert_basis
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T21:26:16.802989+00:00
-- url     : https://prove2.me/theorems/a1ef5e72-84f2-4585-a1e2-63a8bdde69ba
-- title:
--   Existence of Hilbert bases
-- statement:
--   **Existence of Hilbert bases.** Every Hilbert space $E$ over $\mathbb R$ or $\mathbb C$ has a Hilbert basis: an orthonormal family $(e_i)_{i\in w}$, $w\subseteq E$, whose closed linear span is $E$, so that every $x\in E$ has the expansion $x=\sum_i\langle e_i,x\rangle e_i$ with $\|x\|^2=\sum_i|\langle e_i,x\rangle|^2$.
--
--   Hence every Hilbert space is isometrically isomorphic to $\ell^2(w)$ for some index set $w$. This is the structural foundation of Fourier series and of spectral theory. The proof uses Zorn's lemma to find a maximal orthonormal set.
--
--   **Formalization note.** Mathlib's `exists_hilbertBasis`. `HilbertBasis w 𝕜 E` is a linear isometric equivalence of `E` with `ℓ²(w, 𝕜)`. The condition `⇑b = ((↑) : w → E)` says the basis vectors are exactly the elements of the set `w`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `exists_hilbertBasis`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem exists_hilbert_basis (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] :
    ∃ (w : Set E) (b : HilbertBasis w 𝕜 E), ⇑b = ((↑) : w → E) := by sorry

end FamousTheorems
