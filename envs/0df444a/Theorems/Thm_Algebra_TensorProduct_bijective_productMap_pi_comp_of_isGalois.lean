-- Prove2me | Theorems.Thm_Algebra_TensorProduct_bijective_productMap_pi_comp_of_isGalois
-- name    : Algebra.TensorProduct.bijective_productMap_pi_comp_of_isGalois
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/0f6d9ae5-bb28-5919-aa3a-5689590c155a
-- title:
--   Splitting of L⊗_K F over a Galois extension
-- statement:
--   Let $K$, $L$ and $F$ be fields, with $L$ and $F$ both $K$-algebras, and assume $L$ is finite-dimensional over $K$ and $L/K$ is Galois. Let $\sigma_0 : L \to F$ be a $K$-algebra homomorphism. Consider the two $K$-algebra homomorphisms into the product algebra $\prod_{\tau \in \mathrm{Gal}(L/K)} F$, indexed by the group $L \simeq_{\mathrm{alg}[K]} L$ of $K$-algebra automorphisms of $L$: the map $L \to \prod_\tau F$ whose $\tau$-component is $\sigma_0 \circ \tau$ (the composite of the underlying $K$-algebra homomorphism of $\tau$ with $\sigma_0$), and the diagonal map $F \to \prod_\tau F$ all of whose components are the identity of $F$, each assembled componentwise by `Pi.algHom`. The assertion is that the induced homomorphism on the tensor product, $\mathrm{productMap}$ of these two maps, is bijective as a function. Explicitly, the map $L \otimes_K F \to \prod_{\tau} F$ sending $\ell \otimes f$ to $(\sigma_0(\tau \ell)\, f)_{\tau}$ is a bijection.
--
--   This is the classical statement that a finite Galois extension splits completely after base change to any field $F$ admitting a $K$-embedding of $L$: $L \otimes_K F \cong F^{[L:K]}$, with the factors indexed by $\mathrm{Gal}(L/K)$. It is used to compute norms from $L \otimes_K F$ as products over the Galois group, in [`Algebra.TensorProduct.algebraMap_norm_eq_prod_congr_apply_of_isGalois`](thm.html#Algebra.TensorProduct.algebraMap_norm_eq_prod_congr_apply_of_isGalois).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_TensorProduct_bijective_productMap_pi_comp_of_isGalois.lean

import Mathlib
import Definitions.Def_Mathlib_RightActionInstances

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.TensorProduct.bijective_productMap_pi_comp_of_isGalois
    (K L F : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Field F] [Algebra K F] (σ₀ : L →ₐ[K] F) :
    Function.Bijective
      (Algebra.TensorProduct.productMap
        (Pi.algHom K (fun _ : L ≃ₐ[K] L => F) (fun τ : L ≃ₐ[K] L => σ₀.comp (τ : L →ₐ[K] L)))
        (Pi.algHom K (fun _ : L ≃ₐ[K] L => F) (fun _ : L ≃ₐ[K] L => AlgHom.id K F))) := by sorry
