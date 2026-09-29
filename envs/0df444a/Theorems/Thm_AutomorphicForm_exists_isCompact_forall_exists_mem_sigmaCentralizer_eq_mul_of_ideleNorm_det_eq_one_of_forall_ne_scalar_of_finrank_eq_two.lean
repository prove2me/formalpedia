-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isCompact_forall_exists_mem_sigmaCentralizer_eq_mul_of_ideleNorm_det_eq_one_of_forall_ne_scalar_of_finrank_eq_two
-- name    : AutomorphicForm.exists_isCompact_forall_exists_mem_sigmaCentralizer_eq_mul_of_ideleNorm_det_eq_one_of_forall_ne_scalar_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/749c2732-73a4-5412-b60b-42d0f59a8a24
-- title:
--   Fujisaki compactness for twisted centralizers of second-kind GL₂ classes
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ Galois of degree $2$, and let $\sigma$ be a $K$-algebra automorphism of $L$ such that every element of $\mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$. Fix $\delta_0 \in \mathrm{GL}_2(L)$, a unit $c$ of $L \otimes_K \mathbb{A}_K$ (where $\mathbb{A}_K$ is the adele ring of $K$) and an idele unit $u \in \mathbb{A}_K^\times$, and put $\delta = (\delta_0 \otimes 1)\cdot c\,\mathrm{Id}$ in $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$, the first factor being the image of $\delta_0$ under $l \mapsto l \otimes 1$ and the second the scalar matrix of $c$. Assume: (i) the $\sigma$-norm string of $\delta$, namely the product $\prod_{i<[L:K]} \sigma^i(\delta)$ with $\sigma$ acting on $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$ through the left tensor factor, equals the image of the scalar matrix $\mathrm{diag}(u,u) \in \mathrm{GL}_2(\mathbb{A}_K)$ under $a \mapsto 1 \otimes a$; and (ii) $\delta_0$ is $\sigma$-conjugate to no scalar matrix, i.e. $x^{-1}\delta_0\,\sigma(x) \neq z\,\mathrm{Id}$ for all $x \in \mathrm{GL}_2(L)$ and $z \in L^\times$. Let $T$ be the $\sigma$-twisted centralizer $\{t : t\delta\,\sigma(t)^{-1} = \delta\}$, a subgroup of $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$. Then there is a compact subset $C$ of $T$ such that every $t \in T$ whose determinant, read in $\mathrm{GL}_2(\mathbb{A}_L)$ through the ring isomorphism $L \otimes_K \mathbb{A}_K \cong \mathbb{A}_K \otimes_K L \cong \mathbb{A}_L$, has idelic norm $1$ (the value of the distributive Haar character of $\mathbb{A}_L$ at it) factors as $t = (\gamma \otimes 1)\cdot k$ with $\gamma \in \mathrm{GL}_2(L)$ satisfying $\gamma\delta_0\,\sigma(\gamma)^{-1} = \delta_0$ and $k \in C$.
--
--   This is Fujisaki's compactness lemma in the form needed for twisted orbital integrals: under the two hypotheses the twisted centralizer is the idele group of a quaternion division algebra over $K$ and its norm-one part is compact modulo the rational points. It is used in the computation of the measure of a fundamental domain for the rational points acting on the part of the twisted centralizer with idelic determinant norm in a bounded interval, where the answer is a multiple of a logarithm.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isCompact_forall_exists_mem_sigmaCentralizer_eq_mul_of_ideleNorm_det_eq_one_of_forall_ne_scalar_of_finrank_eq_two.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_isCompact_forall_exists_mem_sigmaCentralizer_eq_mul_of_ideleNorm_det_eq_one_of_forall_ne_scalar_of_finrank_eq_two
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hN : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ
        (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K u))
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
        Matrix.GeneralLinearGroup.scalar (Fin 2) z) :
    ∃ C : Set (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
        (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)),
      IsCompact C ∧
        ∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
            (Matrix.GeneralLinearGroup.map
                (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
              Matrix.GeneralLinearGroup.scalar (Fin 2) c),
          NumberField.TateGlobal.ideleNorm L
            (Matrix.GeneralLinearGroup.det
              (Matrix.GeneralLinearGroup.map
                (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                  (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
                (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) = 1 →
          ∃ γ ∈ AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀,
            ∃ k ∈ C,
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) =
                Matrix.GeneralLinearGroup.map
                    (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) γ *
                  (k : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) := by sorry
