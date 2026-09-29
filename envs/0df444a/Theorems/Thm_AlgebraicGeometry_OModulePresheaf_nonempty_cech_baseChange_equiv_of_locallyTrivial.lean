-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cech_baseChange_equiv_of_locallyTrivial
-- name    : AlgebraicGeometry.OModulePresheaf.nonempty_cech_baseChange_equiv_of_locallyTrivial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/f938e03a-999e-54a0-af1d-6b86224921fd
-- title:
--   Base change of Čech cohomology of a locally trivial module
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme and $\pi\colon X\to\operatorname{Spec}R$ a separated morphism; let $\mathcal U$ be an ordered affine cover of $X$, that is, a finite linearly ordered index type together with affine opens $U_i$ whose supremum is $\top$, and let $M$ be a sheaf of $\mathcal O_X$-modules. Assume $M$ is locally trivial in the sense that every point of $X$ lies in an open $V$ for which the pullback of $M$ along the inclusion $V\hookrightarrow X$ is isomorphic to the unit sheaf of modules $\mathcal O_V$. Let $A$ be a commutative $R$-algebra. Write $(\check C^\bullet,d^\bullet)$ for the alternating Čech complex of the presheaf `ofModules π M` (the open $U\mapsto\Gamma(M,U)$ with its $R$- and $\Gamma(X,U)$-module structures and restriction maps) on $\mathcal U$, and let $X_A=X\times_{\operatorname{Spec}R}\operatorname{Spec}A$, with structure morphism the second projection, carry the pullback of $M$ along the first projection and the cover obtained by taking preimages of the $U_i$. The conclusion has two parts. First, unconditionally: there is an $A$-linear isomorphism between $\check H^0$ of the base-changed data, i.e. $\ker$ of its degree-$0$ differential, and $\ker(d^0\otimes_R A)$; and for every $i$ there is a surjective $A$-linear map from $\ker(d^{i+1}\otimes_R A)$ onto $\check H^{i+1}$ of the base-changed data, namely $\ker(d_A^{i+1})$ modulo the part of $\operatorname{im}(d_A^i)$ lying in it, whose kernel is the preimage in $\ker(d^{i+1}\otimes_R A)$ of the range of $d^i\otimes_R A$. Secondly, if $A$ is flat over $R$, then there are $A$-linear isomorphisms $\check H^0(\mathcal U_A,M_A)\cong A\otimes_R\check H^0(\mathcal U,M)$ and $\check H^{i+1}(\mathcal U_A,M_A)\cong A\otimes_R\check H^{i+1}(\mathcal U,M)$ for every $i$. No compatibility of these isomorphisms with further maps is asserted.
--
--   This is the base-change theorem for Čech cohomology computed on a finite ordered affine cover: for a line bundle (a Zariski-locally trivial module) the Čech complex of the base change is the tensor product of the original Čech complex with $A$, so cohomology of the base change is the cohomology of $A\otimes_R\check C^\bullet$, and flatness of $A$ lets one pull $A\otimes_R-$ through kernels and quotients. It is used for the computations of Čech ranks and Euler characteristics under base change, in particular over fields and over local rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cech_baseChange_equiv_of_locallyTrivial.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.OModulePresheaf.nonempty_cech_baseChange_equiv_of_locallyTrivial
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (.of R)) [IsSeparated π]
    (𝒰 : X.OrderedAffineCover) (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (A : Type u) [CommRing A] [Algebra R A] :
    (Nonempty ((OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback
            (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).H0 (𝒰.baseChange π A)
        ≃ₗ[A] LinearMap.ker (((OModulePresheaf.ofModules π M).d 𝒰 0).baseChange A)) ∧
      ∀ i : ℕ, ∃ φ : LinearMap.ker (((OModulePresheaf.ofModules π M).d 𝒰 (i + 1)).baseChange A) →ₗ[A]
          (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback
            (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).HSucc (𝒰.baseChange π A) i,
        Function.Surjective φ ∧
          LinearMap.ker φ = (LinearMap.range (((OModulePresheaf.ofModules π M).d 𝒰 i).baseChange A)).comap
            (LinearMap.ker (((OModulePresheaf.ofModules π M).d 𝒰 (i + 1)).baseChange A)).subtype) ∧
    (Module.Flat R A →
      Nonempty ((OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback
            (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).H0 (𝒰.baseChange π A)
          ≃ₗ[A] A ⊗[R] (OModulePresheaf.ofModules π M).H0 𝒰) ∧
      ∀ i : ℕ, Nonempty ((OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback
            (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).HSucc (𝒰.baseChange π A) i
          ≃ₗ[A] A ⊗[R] (OModulePresheaf.ofModules π M).HSucc 𝒰 i)) := by sorry
