-- Prove2me | Theorems.Thm_AutomorphicForm_exists_normString_scalar_eq_toTensorGL_centralScalar_of_forall_of_finrank_ne_two
-- name    : AutomorphicForm.exists_normString_scalar_eq_toTensorGL_centralScalar_of_forall_of_finrank_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/5a4c9831-7bc9-53ca-8db7-d7cc5cfd0682
-- title:
--   Adelic norm string of a scalar from local data, odd prime degree
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let the degree $n=\operatorname{finrank}_K L$ be prime and different from $2$, and let $\sigma$ be a $K$-algebra automorphism of $L$ with $\sigma\neq 1$. For a commutative $K$-algebra $A$, [`AutomorphicForm.normString K L A σ`](def/AutomorphicForm_TwistedOrbital.html#L205) sends $\delta\in GL_2(L\otimes_K A)$ to the product $\prod_{i=0}^{n-1}\sigma^{i}(\delta)$, where $\sigma$ acts entrywise through the left tensor factor, and [`AutomorphicForm.toTensorGL K L A`](def/AutomorphicForm_TwistedOrbital.html#L71) is the map $GL_2(A)\to GL_2(L\otimes_K A)$ induced by $a\mapsto 1\otimes a$. Let $u$ be a unit of the adele ring of $K$ and let [`AutomorphicForm.centralScalar`](def/AutomorphicForm_AdelicLsXi.html#L18) send $u$ to the scalar matrix $u\cdot I_2$ in $GL_2(\mathbb{A}_K)$. Assume that for every height-one prime $v$ of $\mathcal{O}_K$ there is a unit $z$ of $L\otimes_K K_v$ whose scalar matrix has norm string equal to the image in $GL_2(L\otimes_K K_v)$ of the $v$-component of the finite part of $u\cdot I_2$. The conclusion is that there is a unit $z$ of $L\otimes_K\mathbb{A}_K$ whose scalar matrix in $GL_2(L\otimes_K\mathbb{A}_K)$ has norm string equal to the image of $u\cdot I_2$ under [`AutomorphicForm.toTensorGL`](def/AutomorphicForm_TwistedOrbital.html#L71).
--
--   This is the local-to-adelic passage for norm strings of central (scalar) elements in cyclic base change of odd prime degree, the scalar counterpart of the corresponding statement for regular semisimple elements; it is used in the vanishing statement [`AutomorphicForm.apply_centralScalar_eq_zero_of_not_exists_isNormOf_of_isUnitFactorization_of_prime`](thm.html#AutomorphicForm.apply_centralScalar_eq_zero_of_not_exists_isNormOf_of_isUnitFactorization_of_prime), where the central contributions to the compared trace formulas are analysed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_normString_scalar_eq_toTensorGL_centralScalar_of_forall_of_finrank_ne_two.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_normString_scalar_eq_toTensorGL_centralScalar_of_forall_of_finrank_ne_two
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (hodd : Module.finrank K L ≠ 2)
    (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (u : (AdeleRing (𝓞 K) K)ˣ)
    (hloc : ∀ v : HeightOneSpectrum (𝓞 K), ∃ z : (L ⊗[K] v.adicCompletion K)ˣ,
      AutomorphicForm.normString K L (v.adicCompletion K) σ
          (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
        AutomorphicForm.toTensorGL K L (v.adicCompletion K)
          (AdelicLevel.finComponent (𝓞 K) K v
            (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K u)))) :
    ∃ z : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ,
      AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ
          (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
        AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K)
          (AutomorphicForm.centralScalar (𝓞 K) K u) := by sorry
