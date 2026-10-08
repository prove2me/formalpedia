-- Prove2me | Theorems.Thm_CompOT_NotHilbertian_prop_8_2_centering
-- name    : CompOT.NotHilbertian.prop_8_2_centering
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:33:24.878454+00:00
-- url     : https://prove2.me/theorems/ced42da1-1ec6-462e-b54c-10820a817d3f
-- title:
--   Proof of Proposition 8.2, p. 507 — M fails negative definiteness on zero-sum vectors iff JMJ has a positive eigenvalue
-- statement:
--   Let $M$ be a real $n\times n$ matrix and let $J=I_n-\tfrac1n\mathbb 1_{n,n}$ be the centering matrix. Assume $JMJ$ is symmetric (as it is when $M$ is). Then
--   $$\exists\,r\in\mathbb R^n,\ \sum_ir_i=0,\ r^\top Mr>0\iff JMJ\text{ has a positive eigenvalue}.$$
--
--   In the proof of Proposition 8.2 this is applied to $M=\mathbf D_p^2$, the entrywise square of the matrix of pairwise Wasserstein distances between the 35 grid measures, so that failure of negative definiteness can be read off the spectrum of $J\mathbf D_p^2J$ (Figure 8.6).
--
--   **Formalization Note** The eigenvalues are those of the symmetric matrix $JMJ$ (`Matrix.IsHermitian.eigenvalues`), so the symmetry of $JMJ$ is a hypothesis; it is implied by the symmetry of $M$. For $n=0$ both sides are false.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), proof of Proposition 8.2, p. 507 (centering matrix criterion)

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance
import Definitions.Def_CompOT_NotHilbertian_Defs

namespace CompOT.NotHilbertian

open Matrix

/-- Proof of Proposition 8.2, p. 507: a matrix `M` (there `M = D_p²`) fails the
negative-definiteness inequality on zero-sum vectors if and only if `J M J` has a positive
eigenvalue, where `J = Iₙ - (1/n) 𝟙_{n,n}` is the centering matrix. -/
theorem prop_8_2_centering {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hH : (centering n * M * centering n).IsHermitian) :
    (¬ ∀ r : Fin n → ℝ, ∑ i, r i = 0 → r ⬝ᵥ (M *ᵥ r) ≤ 0) ↔ ∃ i, 0 < hH.eigenvalues i := by sorry

end CompOT.NotHilbertian
