-- Prove2me | Theorems.Thm_AutomorphicForm_twistedCentralizer_diagUnits2_eq_map_toTensorGL_centralizer_of_normString_eq_of_isUnit_sub
-- name    : AutomorphicForm.twistedCentralizer_diagUnits2_eq_map_toTensorGL_centralizer_of_normString_eq_of_isUnit_sub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/637658e7-1771-5f36-8f24-fa72012ac810
-- title:
--   Twisted centraliser of a norm-exact diagonal element
-- statement:
--   Let $K$ and $L$ be fields with $L$ a finite Galois extension of $K$, and let $\sigma$ be a $K$-algebra automorphism of $L$ such that every $\tau \in \mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$ (so $L/K$ is cyclic with generator $\sigma$). Let $A$ be a commutative ring equipped with a $K$-algebra structure, let $x, y \in A^{\times}$ be such that $x - y$ is a unit of $A$, and let $d_1, d_2 \in (L \otimes_K A)^{\times}$. Write $\mathrm{diag}(u,v)$ for the element `diagUnits2` of the general linear group of $2 \times 2$ matrices with diagonal entries $u, v$ and the evident inverse, and let `toTensorGL` be the homomorphism $\mathrm{GL}_2(A) \to \mathrm{GL}_2(L \otimes_K A)$ induced entrywise by $a \mapsto 1 \otimes a$. Assume the twisted norm string of $\delta = \mathrm{diag}(d_1,d_2)$, namely the product $\delta \cdot \sigma(\delta) \cdots \sigma^{[L:K]-1}(\delta)$, where $\sigma$ acts entrywise through the left tensor factor, equals the image of $\mathrm{diag}(x,y)$ under `toTensorGL` (an exact equality, not merely up to conjugacy). Then the twisted centraliser of $\delta$, that is the subgroup $\{ t \in \mathrm{GL}_2(L \otimes_K A) : t \,\delta\, \sigma(t)^{-1} = \delta \}$, coincides with the image under `toTensorGL` of the centraliser of $\mathrm{diag}(x,y)$ in $\mathrm{GL}_2(A)$.
--
--   This is the descent step in the comparison of twisted and ordinary orbital integrals for $\mathrm{GL}(2)$ in cyclic base change: for a diagonal element whose twisted norm is exactly a diagonal matrix over the base with regular difference of eigenvalues, the $\sigma$-centraliser contains no more than the base-field torus. It is used in the analysis of twisted weighted orbital integrals attached to $\mathrm{diag}(d_1,d_2)$ and in the construction of torus sections with prescribed norm string.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_twistedCentralizer_diagUnits2_eq_map_toTensorGL_centralizer_of_normString_eq_of_isUnit_sub.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.twistedCentralizer_diagUnits2_eq_map_toTensorGL_centralizer_of_normString_eq_of_isUnit_sub
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (A : Type) [CommRing A] [Algebra K A]
    (x y : Aˣ) (hxy : IsUnit ((x : A) - (y : A)))
    (d₁ d₂ : (L ⊗[K] A)ˣ)
    (hN : AutomorphicForm.normString K L A σ (diagUnits2 d₁ d₂) = AutomorphicForm.toTensorGL K L A (diagUnits2 x y)) :
    AutomorphicForm.twistedCentralizer K L A σ (diagUnits2 d₁ d₂) =
      (Subgroup.centralizer ({diagUnits2 x y} : Set (GL (Fin 2) A))).map (AutomorphicForm.toTensorGL K L A) := by sorry
