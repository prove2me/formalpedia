-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_algEquiv_tensor_sections_pullback_fst_preimage_of_isAffineOpen
-- name    : AlgebraicGeometry.Scheme.exists_algEquiv_tensor_sections_pullback_fst_preimage_of_isAffineOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/d260ed93-5ef9-52bd-9885-61bd9da58a66
-- title:
--   Affine base change of sections over an affine open
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, $c\colon X \to \operatorname{Spec} R$ a morphism, $U \subseteq X$ an open subscheme assumed to be an affine open, and $A$ a commutative $R$-algebra. Write $\operatorname{Spec} A \to \operatorname{Spec} R$ for the morphism induced by $\operatorname{algebraMap} R A$, and form the fibre product $P = X \times_{\operatorname{Spec} R} \operatorname{Spec} A$ with its two projections. Two algebra structures are installed by the construction `Scheme.TwoAffineOpenCover.algebraOfHom`, which turns a morphism to an affine scheme into an algebra structure on sections over an open: $\Gamma(X, U)$ becomes an $R$-algebra via the ring map $\Gamma(\operatorname{Spec} R, \top) \cong R$ followed by $c^{\sharp}\colon \Gamma(X,\top) \to \Gamma(X,U)$, and $\Gamma(P, \mathrm{pr}_1^{-1}U)$ becomes an $A$-algebra via the same recipe applied to the projection $\mathrm{pr}_2\colon P \to \operatorname{Spec} A$ and the open $\mathrm{pr}_1^{-1}U$. The assertion is that there exists an isomorphism of $A$-algebras $e\colon A \otimes_R \Gamma(X,U) \xrightarrow{\ \sim\ } \Gamma(P, \mathrm{pr}_1^{-1}U)$, the source carrying the usual base-change $A$-algebra structure, such that for every section $s \in \Gamma(X,U)$ one has $e(1 \otimes s) = \mathrm{pr}_1^{\sharp}(s)$, the image of $s$ under the map on sections over $U$ induced by $\mathrm{pr}_1$.
--
--   This is the affine base change statement for sections over an affine open: the preimage of $U$ in $X \times_{\operatorname{Spec} R} \operatorname{Spec} A$ is affine with coordinate ring $A \otimes_R \Gamma(X,U)$, with the isomorphism pinned down on the generators $1 \otimes s$. It is used in the variant with the tensor factors in the other order and in the finiteness and rank computations for base changes of the kernel scheme attached to a relative group law on a Jacobian with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_algEquiv_tensor_sections_pullback_fst_preimage_of_isAffineOpen.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.exists_algEquiv_tensor_sections_pullback_fst_preimage_of_isAffineOpen
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    (c : X ⟶ Spec (.of R)) (U : X.Opens) (hU : IsAffineOpen U) (A : Type u) [CommRing A] [Algebra R A] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))
      ((Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A)) ⁻¹ᵁ U)
    ∃ e : (A ⊗[R] Γ(X, U)) ≃ₐ[A]
        Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A),
          (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A)) ⁻¹ᵁ U),
      ∀ s : Γ(X, U), e ((1 : A) ⊗ₜ[R] s) =
        ((Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A)).app U).hom s := by sorry
