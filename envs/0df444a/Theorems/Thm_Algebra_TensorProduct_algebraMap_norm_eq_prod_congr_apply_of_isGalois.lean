-- Prove2me | Theorems.Thm_Algebra_TensorProduct_algebraMap_norm_eq_prod_congr_apply_of_isGalois
-- name    : Algebra.TensorProduct.algebraMap_norm_eq_prod_congr_apply_of_isGalois
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/04d70c17-5432-51fb-a254-c3631e9656cc
-- title:
--   Base-changed norm equals product of Galois conjugates
-- statement:
--   Let $K$, $L$ and $E$ be fields with $L$ and $E$ both $K$-algebras, $L$ finite-dimensional over $K$ and $L/K$ Galois, and consider the tensor product $L \otimes_K E$, regarded as an $E$-algebra through its right factor (the scoped right-action algebra structure, under which $e \in E$ acts as $1 \otimes e$). The assertion is that for every $x \in L \otimes_K E$ the image in $L \otimes_K E$ of the algebra norm $N_{(L \otimes_K E)/E}(x) \in E$ under the structure map $E \to L \otimes_K E$ equals the product, over all $K$-algebra automorphisms $\tau$ of $L$, of the elements $(\tau \otimes \mathrm{id}_E)(x)$, where $\tau \otimes \mathrm{id}_E$ denotes `Algebra.TensorProduct.congr` applied to $\tau$ and the identity automorphism of $E$; the product is taken over the (finite) group $L \simeq_{\mathrm{alg}[K]} L$, whose order is $[L : K]$. Thus the norm of $x$ down to $E$, viewed inside $L \otimes_K E$, is the product of the Galois conjugates of $x$ taken in the left factor.
--
--   This is the base change to an arbitrary $K$-algebra field $E$ of the classical formula $N_{L/K}(y) = \prod_{\tau \in \mathrm{Gal}(L/K)} \tau(y)$, now for all elements of $L \otimes_K E$ rather than those of the form $y \otimes 1$. It is used in the analysis of norm-one units and compactness statements for adelic quaternionic automorphic forms, where norms of elements of $L \otimes_K E$ must be compared with their Galois translates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_TensorProduct_algebraMap_norm_eq_prod_congr_apply_of_isGalois.lean

import Mathlib
import Definitions.Def_Mathlib_RightActionInstances

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open scoped TensorProduct.RightActions in

theorem Algebra.TensorProduct.algebraMap_norm_eq_prod_congr_apply_of_isGalois
    (K L E : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Field E] [Algebra K E] (x : L ⊗[K] E) :
    algebraMap E (L ⊗[K] E) (Algebra.norm E x) =
      ∏ τ : L ≃ₐ[K] L, Algebra.TensorProduct.congr τ (AlgEquiv.refl : E ≃ₐ[K] E) x := by sorry
