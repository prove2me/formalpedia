-- Prove2me | Theorems.Thm_AutomorphicForm_isNormOf_scalar_tensorPlace_of_normString_eq_toTensorGL_centralScalar
-- name    : AutomorphicForm.isNormOf_scalar_tensorPlace_of_normString_eq_toTensorGL_centralScalar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/fed732c4-8d75-5dc4-851c-cb0944584b64
-- title:
--   Norm-string identity at a finite place: scalar is a σ-norm
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $\sigma$ be a $K$-algebra automorphism of $L$, let $\delta \in \mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$, where $\mathbb{A}_K$ is the adele ring of $K$, and let $u \in \mathbb{A}_K^{\times}$. Write $\mathrm{normString}$ for the product $\prod_{i=0}^{n-1} (\mathrm{sigmaGL}\,\sigma)^{i}(\delta)$ with $n = \mathrm{finrank}_K L$, the factors taken in increasing order of $i$, where $\mathrm{sigmaGL}$ is the automorphism of $\mathrm{GL}_2(L \otimes_K A)$ induced entrywise by $\sigma \otimes \mathrm{id}$, and write $\mathrm{toTensorGL}$ for the homomorphism $\mathrm{GL}_2(A) \to \mathrm{GL}_2(L \otimes_K A)$ induced by $a \mapsto 1 \otimes a$. Assume this norm string equals the image under $\mathrm{toTensorGL}$ of the scalar matrix $u \cdot 1_2 \in \mathrm{GL}_2(\mathbb{A}_K)$. Then for every $v$ in the height-one spectrum of $\mathcal{O}_K$, the element $\mathrm{tensorPlace}\,\delta \in \mathrm{GL}_2(L \otimes_K K_v)$ — the image of $\delta$ under the map induced by $\mathrm{id}_L \otimes (\text{evaluation of the finite-adelic part at } v)$ — satisfies $\mathrm{IsNormOf}$ for the scalar matrix $u_v \cdot 1_2 \in \mathrm{GL}_2(K_v)$, where $u_v$ is the image of $u$ in $(K_v)^{\times}$: that is, there exists $y \in \mathrm{GL}_2(L \otimes_K K_v)$ with $\mathrm{toTensorGL}(u_v \cdot 1_2) = y^{-1} \cdot \mathrm{normString}\,\sigma\,(\mathrm{tensorPlace}\,\delta) \cdot y$.
--
--   This is the localisation at a finite place of the global twisted-norm condition: a $\sigma$-norm-string identity over the adeles for a central scalar implies, place by place, that the local component of $\delta$ has the corresponding local scalar as a $\sigma$-norm. It is used by the local computations of set integrals of $\lambda$-type over lattice and closure regions in the non-$\sigma$-conjugate-to-a-scalar case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isNormOf_scalar_tensorPlace_of_normString_eq_toTensorGL_centralScalar.lean

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem AutomorphicForm.isNormOf_scalar_tensorPlace_of_normString_eq_toTensorGL_centralScalar
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L)
    (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hN : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ =
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K u))
    (v : HeightOneSpectrum (𝓞 K)) :
    AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ
      (Matrix.GeneralLinearGroup.scalar (Fin 2)
        (Units.map ((AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom) u))
      (AutomorphicForm.tensorPlace K L v δ) := by sorry
