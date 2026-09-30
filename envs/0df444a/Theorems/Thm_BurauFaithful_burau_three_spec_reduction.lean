-- Prove2me | Theorems.Thm_BurauFaithful_burau_three_spec_reduction
-- name    : BurauFaithful.burau_three_spec_reduction
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-29T17:20:33.72235+00:00
-- url     : https://prove2.me/theorems/8b882658-fd29-4aad-8dd5-7e5b3a944c4d
-- title:
--   Two-dimensional reduction of the Burau representation at $t=-1$ (trivial $\oplus$ reduced)
-- statement:
--   This is the 2-dimensional reduction of the unreduced Burau representation, at the specialization $t=-1$ used in Birman's proof of Theorem 3.15 (J. S. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82, §3.3, pp. 129-130).
--
--   The unreduced Burau representation $\rho_3$ of $B_3$ acts on $\mathbb Z[t,t^{-1}]^3$. It fixes the vector $v=(1,1,1)$ and the covector $w=(1,t,t^2)$, and $w\cdot v = 1+t+t^2$. Hence the representation is the direct sum of the trivial representation on $\langle v\rangle$ and the (2-dimensional) reduced Burau representation on $w^\perp$; the basis $[\,v \mid (t,-1,0) \mid (t^2,0,-1)\,]$ realizes this splitting.
--
--   At $t=-1$ that basis is the integral matrix
--
--   $$C = \begin{pmatrix} 1 & -1 & 1\\ 1 & -1 & 0\\ 1 & 0 & -1\end{pmatrix},\qquad \det C = (1+t+t^2)\big|_{t=-1} = 1,$$
--
--   so $C$ is invertible over $\mathbb Z$. The theorem states that conjugation by $C$ brings the specialized Burau matrices of the two generators into block form "trivial $\oplus$ reduced":
--
--   $$C^{-1}\,\rho_3(\sigma_1)\big|_{t=-1}\,C = \begin{pmatrix} 1&0&0\\ 0&1&-1\\ 0&0&1\end{pmatrix},\qquad
--   C^{-1}\,\rho_3(\sigma_2)\big|_{t=-1}\,C = \begin{pmatrix} 1&0&0\\ 0&2&-1\\ 0&1&0\end{pmatrix}.$$
--
--   Consequently the kernel of the specialized 3-dimensional representation coincides with the kernel of the specialized 2-dimensional reduced Burau representation, which is the setting of the classical computation $\ker(\rho_3|_{t=-1})=\langle\Delta^4\rangle$.
--
--   **Formalization Note** The specialization is written inline as `LaurentPolynomial.eval₂ (Int.castRingHom ℤ) (-1 : ℤˣ)` and extended to matrices by `Matrix.GeneralLinearGroup.map`; the matrices displayed are written as matrix literals `!![...]`.
-- source:
--   J. S. Birman, *Braids, Links, and Mapping Class Groups*, Ann. of Math. Studies 82, Princeton Univ. Press, 1974, Chapter 3, §3.3, Theorem 3.15, pp. 129-130 (the modular group and the specialization t = -1); cf. C. Kassel, V. Turaev, *Braid Groups*, GTM 247, Chapter 3 (the reduced Burau representation as a direct summand of the unreduced one).

import Definitions.Def_BurauFaithful_UnreducedBurau

set_option autoImplicit false

theorem BurauFaithful.burau_three_spec_reduction :
    ((Matrix.GeneralLinearGroup.map (LaurentPolynomial.eval₂ (Int.castRingHom ℤ) (-1 : ℤˣ))
          (BurauFaithful.burauRep 3 (BraidsLinksMCG.sigma (n := 3) ⟨0, by decide⟩)) :
        Matrix (Fin 3) (Fin 3) ℤ) * !![1, -1, 1; 1, -1, 0; 1, 0, -1] =
      !![1, -1, 1; 1, -1, 0; 1, 0, -1] * !![1, 0, 0; 0, 1, -1; 0, 0, 1]) ∧
    ((Matrix.GeneralLinearGroup.map (LaurentPolynomial.eval₂ (Int.castRingHom ℤ) (-1 : ℤˣ))
          (BurauFaithful.burauRep 3 (BraidsLinksMCG.sigma (n := 3) ⟨1, by decide⟩)) :
        Matrix (Fin 3) (Fin 3) ℤ) * !![1, -1, 1; 1, -1, 0; 1, 0, -1] =
      !![1, -1, 1; 1, -1, 0; 1, 0, -1] * !![1, 0, 0; 0, 2, -1; 0, 1, 0]) := by sorry
