-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_map_restrictAlgHom_eq_presheaf_map_of_tmul_eq
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.map_restrictAlgHom_eq_presheaf_map_of_tmul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/17d8c97e-15da-5732-9d06-bb09e3bf9559
-- title:
--   Pinned maps on relative charts commute with restriction
-- statement:
--   Let $R$ and $A$ be commutative rings with $A$ an $R$-algebra, let $X$ and $Y$ be schemes, and let $\pi : X \to \operatorname{Spec} R$, $p : Y \to X$ and $\pi_A : Y \to \operatorname{Spec} A$ be morphisms of schemes. Fix opens $U' \le U$ of $X$ and opens $W' \le W$ of $Y$ with $W \le p^{-1}U$ and $W' \le p^{-1}U'$. Each section ring $\Gamma(X,U)$ is an $R$-algebra via the ring map $\Gamma(\operatorname{Spec} R) \cong R \to \Gamma(X,U)$ obtained from $\pi$ (the composite of the inverse of the $\Gamma$–$\operatorname{Spec}$ isomorphism with $\pi$'s local section map $\pi^{\sharp}_{\top,U}$), and likewise $\Gamma(Y,W)$, $\Gamma(Y,W')$ are $A$-algebras via $\pi_A$. Let $\sigma : A \otimes_R \Gamma(X,U) \to \Gamma(Y,W)$ and $\sigma' : A \otimes_R \Gamma(X,U') \to \Gamma(Y,W')$ be ring homomorphisms that are pinned in the sense that $\sigma(1 \otimes x)$ is the restriction to $W$ of $p^{\sharp}_U(x)$ for all $x \in \Gamma(X,U)$, $\sigma(a \otimes 1) = \operatorname{algebraMap}_A^{\Gamma(Y,W)}(a)$ for all $a \in A$, and the two analogous identities hold for $\sigma'$ with $U'$, $W'$. Then for every $y \in A \otimes_R \Gamma(X,U)$ one has $\sigma'\bigl((\mathrm{id}_A \otimes \mathrm{res}^U_{U'})(y)\bigr) = \sigma(y)|_{W'}$, where $\mathrm{res}^U_{U'}$ is the presheaf restriction of $X$ viewed as an $R$-algebra map (`restrictAlgHom`) and $\sigma(y)|_{W'}$ is the presheaf restriction of $Y$ along $W' \le W$.
--
--   This is the naturality, under shrinking of the opens, of maps $A \otimes_R \Gamma(X,U) \to \Gamma(Y,W)$ pinned by the two conditions on $a \otimes 1$ and $1 \otimes x$ — the situation of a base change $Y = X \times_{\operatorname{Spec} R} \operatorname{Spec} A$ with its two projections, although no pullback hypothesis is imposed and $U$, $W$ need not be affine nor $\sigma$, $\sigma'$ bijective. It serves the Čech-level bookkeeping in the deformation-theoretic work on good reduction of Jacobians, where chart identifications must be compared after restriction to smaller opens.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_map_restrictAlgHom_eq_presheaf_map_of_tmul_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.TwoAffineOpenCover TensorProduct

universe u

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.map_restrictAlgHom_eq_presheaf_map_of_tmul_eq
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {X Y : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of R)) (p : Y ⟶ X) (πA : Y ⟶ Spec (CommRingCat.of A))
    {U U' : X.Opens} (h : U' ≤ U) {W W' : Y.Opens} (hW : W ≤ p ⁻¹ᵁ U) (hW' : W' ≤ p ⁻¹ᵁ U') (hWW : W' ≤ W)
    (σ : letI := algebraOfHom π U
      A ⊗[R] Γ(X, U) →+* Γ(Y, W))
    (σ' : letI := algebraOfHom π U'
      A ⊗[R] Γ(X, U') →+* Γ(Y, W'))
    (hσ₁ : letI := algebraOfHom π U
      ∀ x : Γ(X, U), σ ((1 : A) ⊗ₜ[R] x) = (Y.presheaf.map (homOfLE hW).op).hom ((p.app U).hom x))
    (hσ₂ : letI := algebraOfHom π U
      letI := algebraOfHom πA W
      ∀ a : A, σ (a ⊗ₜ[R] (1 : Γ(X, U))) = algebraMap A Γ(Y, W) a)
    (hσ'₁ : letI := algebraOfHom π U'
      ∀ x : Γ(X, U'), σ' ((1 : A) ⊗ₜ[R] x) = (Y.presheaf.map (homOfLE hW').op).hom ((p.app U').hom x))
    (hσ'₂ : letI := algebraOfHom π U'
      letI := algebraOfHom πA W'
      ∀ a : A, σ' (a ⊗ₜ[R] (1 : Γ(X, U'))) = algebraMap A Γ(Y, W') a) :
    letI := algebraOfHom π U
    letI := algebraOfHom π U'
    ∀ y : A ⊗[R] Γ(X, U),
      σ' (Algebra.TensorProduct.map (AlgHom.id A A) (restrictAlgHom π h) y) = (Y.presheaf.map (homOfLE hWW).op).hom (σ y) := by sorry
