-- Prove2me | Theorems.Thm_Algebra_TensorProduct_cocycle_trans_symm_of_comparison_identities
-- name    : Algebra.TensorProduct.cocycle_trans_symm_of_comparison_identities
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/c9acd66c-952a-5c15-ac7e-5245c6421556
-- title:
--   Cocycle condition for a transition isomorphism from comparison identities
-- statement:
--   Let $S$ be a commutative ring, $S'$ and $R'$ commutative $S$-algebras, $R''$ a commutative ring that is an algebra over $S' \otimes_S S'$ and over $S$ compatibly (a scalar tower), and $R'''$ a commutative ring that is an algebra over $S' \otimes_S (S' \otimes_S S')$ and over $S$ compatibly. Let $\vartheta_1, \vartheta_2 : R' \to R''$ be $S$-algebra maps, and let $\beta_1 : R' \otimes_S S' \cong R''$ and $\beta_2 : S' \otimes_S R' \cong R''$ be $S$-algebra isomorphisms satisfying $\beta_1(r \otimes t) = \vartheta_1(r)\cdot \mathrm{alg}(1 \otimes t)$ and $\beta_2(s \otimes r) = \mathrm{alg}(s \otimes 1)\cdot \vartheta_2(r)$, where $\mathrm{alg}$ denotes the structure map $S' \otimes_S S' \to R''$. Let $\sigma_{12}, \sigma_{13}, \sigma_{23} : R'' \to R'''$ be $S$-algebra maps which are semilinear over the three coface maps, in the sense that composing the structure map $S' \otimes_S S' \to R''$ with $\sigma_{12}$, $\sigma_{13}$, $\sigma_{23}$ gives the structure map $S' \otimes_S (S' \otimes_S S') \to R'''$ precomposed with $s \otimes t \mapsto s \otimes (t \otimes 1)$, with $s \otimes t \mapsto s \otimes (1 \otimes t)$, and with $x \mapsto 1 \otimes x$ respectively. Assume the comparison identities $\sigma_{13}\circ\vartheta_1 = \sigma_{12}\circ\vartheta_1$, $\sigma_{23}\circ\vartheta_1 = \sigma_{12}\circ\vartheta_2$, $\sigma_{23}\circ\vartheta_2 = \sigma_{13}\circ\vartheta_2$ (pointwise on $R'$), and assume that the $S$-algebra map $R' \otimes_S (S' \otimes_S S') \to R'''$ determined by $\sigma_{12}\circ\vartheta_1$ on $R'$ and by $x \mapsto \mathrm{alg}(1 \otimes x)$ on $S' \otimes_S S'$ is bijective. Then the $S$-algebra isomorphism $\varphi := \beta_2^{-1}\circ\beta_1 : R' \otimes_S S' \cong S' \otimes_S R'$ satisfies the cocycle identity: the composite $(R' \otimes_S S') \otimes_S S' \xrightarrow{\varphi \otimes \mathrm{id}} (S' \otimes_S R') \otimes_S S' \xrightarrow{\mathrm{assoc}} S' \otimes_S (R' \otimes_S S') \xrightarrow{\mathrm{id} \otimes \varphi} S' \otimes_S (S' \otimes_S R')$ equals the composite obtained by first associating to $R' \otimes_S (S' \otimes_S S')$, swapping the two $S'$ factors, associating back, applying $\varphi \otimes \mathrm{id}$, associating, and finally swapping the factors of $R' \otimes_S S'$ in the second slot.
--
--   This is the verification of the cocycle condition for a descent datum: from two identifications $\beta_1, \beta_2$ of $R''$ with base changes of $R'$ and semilinear comparison maps one level up, the resulting transition isomorphism $\varphi = \beta_2^{-1}\beta_1$ is a cocycle on the triple tensor product. It is used by [`AlgebraicGeometry.GradedOAlgebra.IsSectionRing.cocycle_trans_symm_of_cocycle`](thm.html#AlgebraicGeometry.GradedOAlgebra.IsSectionRing.cocycle_trans_symm_of_cocycle) to supply the cocycle hypothesis in the faithfully flat descent of graded algebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_TensorProduct_cocycle_trans_symm_of_comparison_identities.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open TensorProduct Algebra.TensorProduct

theorem Algebra.TensorProduct.cocycle_trans_symm_of_comparison_identities
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
    (R' : Type u) [CommRing R'] [Algebra S R']
    (R'' : Type u) [CommRing R''] [Algebra (S' ⊗[S] S') R''] [Algebra S R''] [IsScalarTower S (S' ⊗[S] S') R'']
    (R''' : Type u) [CommRing R'''] [Algebra (S' ⊗[S] (S' ⊗[S] S')) R'''] [Algebra S R'''] [IsScalarTower S (S' ⊗[S] (S' ⊗[S] S')) R''']
    (ϑ₁ ϑ₂ : R' →ₐ[S] R'')
    (β₁ : R' ⊗[S] S' ≃ₐ[S] R'')
    (hβ₁ : ∀ (r : R') (t : S'), β₁ (r ⊗ₜ t) = ϑ₁ r * algebraMap (S' ⊗[S] S') R'' (1 ⊗ₜ t))
    (β₂ : S' ⊗[S] R' ≃ₐ[S] R'')
    (hβ₂ : ∀ (s : S') (r : R'), β₂ (s ⊗ₜ r) = algebraMap (S' ⊗[S] S') R'' (s ⊗ₜ 1) * ϑ₂ r)
    (σ₁₂ σ₁₃ σ₂₃ : R'' →ₐ[S] R''')
    (hσ₁₂ : σ₁₂.comp (IsScalarTower.toAlgHom S (S' ⊗[S] S') R'') =
      ((IsScalarTower.toAlgHom S (S' ⊗[S] (S' ⊗[S] S')) R''').comp
        (Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S'))))
    (hσ₁₃ : σ₁₃.comp (IsScalarTower.toAlgHom S (S' ⊗[S] S') R'') =
      ((IsScalarTower.toAlgHom S (S' ⊗[S] (S' ⊗[S] S')) R''').comp
        (Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S'))))
    (hσ₂₃ : σ₂₃.comp (IsScalarTower.toAlgHom S (S' ⊗[S] S') R'') =
      ((IsScalarTower.toAlgHom S (S' ⊗[S] (S' ⊗[S] S')) R''').comp
        (Algebra.TensorProduct.includeRight (R := S) (A := S') (B := S' ⊗[S] S'))))
    (hA : ∀ x : R', σ₁₃ (ϑ₁ x) = σ₁₂ (ϑ₁ x)) (hB : ∀ x : R', σ₂₃ (ϑ₁ x) = σ₁₂ (ϑ₂ x))
    (hC : ∀ x : R', σ₂₃ (ϑ₂ x) = σ₁₃ (ϑ₂ x))
    (hbij : Function.Bijective
      (Algebra.TensorProduct.lift (σ₁₂.comp ϑ₁)
        ((IsScalarTower.toAlgHom S (S' ⊗[S] (S' ⊗[S] S')) R''').comp
          (Algebra.TensorProduct.includeRight (R := S) (A := S') (B := S' ⊗[S] S')))
        (fun _ _ => Commute.all _ _) : R' ⊗[S] (S' ⊗[S] S') →ₐ[S] R''')) :
    let φ : R' ⊗[S] S' ≃ₐ[S] S' ⊗[S] R' := β₁.trans β₂.symm
    (Algebra.TensorProduct.map (AlgHom.id S S') φ.toAlgHom).comp
        ((Algebra.TensorProduct.assoc S S S S' R' S').toAlgHom.comp
          (Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id S S'))) =
      (Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.comm S R' S').toAlgHom).comp
        ((Algebra.TensorProduct.assoc S S S S' R' S').toAlgHom.comp
          ((Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id S S')).comp
            ((Algebra.TensorProduct.assoc S S S R' S' S').symm.toAlgHom.comp
              ((Algebra.TensorProduct.map (AlgHom.id S R') (Algebra.TensorProduct.comm S S' S').toAlgHom).comp
                (Algebra.TensorProduct.assoc S S S R' S' S').toAlgHom)))) := by sorry
