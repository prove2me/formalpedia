-- Prove2me | Theorems.Thm_Algebra_TensorProduct_map_norm_eq_norm_map_of_rightAlgebra
-- name    : Algebra.TensorProduct.map_norm_eq_norm_map_of_rightAlgebra
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/959f2c3f-79d6-501d-b419-434c894c31e0
-- title:
--   Norms commute with base change along ι : E → F
-- statement:
--   Let $K$ be a field, $L$ a field extension of $K$ that is finite-dimensional as a $K$-vector space, and let $E$ and $F$ be fields equipped with $K$-algebra structures. Let $\iota : E \to F$ be a $K$-algebra homomorphism and let $x \in L \otimes_K E$. The scoped right-action instances are in force, so that $L \otimes_K E$ is regarded as an algebra over the right tensor factor $E$, and likewise $L \otimes_K F$ as an $F$-algebra; the norms are taken with respect to these structures. The assertion is that
--   $$\iota\bigl(N_{L \otimes_K E / E}(x)\bigr) = N_{L \otimes_K F / F}\bigl((\mathrm{id}_L \otimes \iota)(x)\bigr),$$
--   where $\mathrm{id}_L \otimes \iota$ denotes the $K$-algebra homomorphism $L \otimes_K E \to L \otimes_K F$ obtained by functoriality of the tensor product from the identity of $L$ and from $\iota$, and where $N$ denotes the algebra norm, i.e. the determinant of the left multiplication map viewed as an endomorphism of the relevant finite free module.
--
--   This is the compatibility of the algebra norm of $L \otimes_K E$ over $E$ with base change along a $K$-algebra map $E \to F$, in the convention in which the tensor product is an algebra over its right factor. It is used in the Galois-theoretic description of such norms, being cited by [`Algebra.TensorProduct.algebraMap_norm_eq_prod_congr_apply_of_isGalois`](thm.html#Algebra.TensorProduct.algebraMap_norm_eq_prod_congr_apply_of_isGalois), and serves the semi-local vocabulary in which $L \otimes_K K_v$ is treated as a $K_v$-algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_TensorProduct_map_norm_eq_norm_map_of_rightAlgebra.lean

import Mathlib
import Definitions.Def_Mathlib_RightActionInstances

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

open scoped TensorProduct.RightActions in

theorem Algebra.TensorProduct.map_norm_eq_norm_map_of_rightAlgebra
    (K L E F : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Field E] [Algebra K E] [Field F] [Algebra K F] (ι : E →ₐ[K] F) (x : L ⊗[K] E) :
    ι (Algebra.norm E x) =
      Algebra.norm F (Algebra.TensorProduct.map (AlgHom.id K L) ι x) := by sorry
