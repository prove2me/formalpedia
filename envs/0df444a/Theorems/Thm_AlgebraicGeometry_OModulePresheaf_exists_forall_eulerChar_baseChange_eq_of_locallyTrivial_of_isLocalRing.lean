-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_eulerChar_baseChange_eq_of_locallyTrivial_of_isLocalRing
-- name    : AlgebraicGeometry.OModulePresheaf.exists_forall_eulerChar_baseChange_eq_of_locallyTrivial_of_isLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/e0ba6fa6-dae6-571b-b391-e5970409e643
-- title:
--   Constancy of the Čech Euler characteristic over a local base
-- statement:
--   Let $R$ be a Noetherian local ring, let $X$ be a scheme and let $\pi : X \to \operatorname{Spec} R$ be proper and flat. Let $M$ be an $\mathcal O_X$-module, assumed locally trivial in the sense that every point of $X$ has an open neighbourhood $U$ for which the pullback of $M$ along the inclusion $U \hookrightarrow X$ is isomorphic to the unit sheaf of modules `SheafOfModules.unit` on $U$. Let $\mathcal U$ be an `OrderedAffineCover` of $X$: a finite linearly ordered family $(U_i)_{i \in \iota}$ of affine opens with $\bigsqcup_i U_i = \top$. Then there is an integer $\chi_0$ such that for every field $A$ equipped with an $R$-algebra structure the following holds. Form the pullback $X_A = X \times_{\operatorname{Spec} R} \operatorname{Spec} A$ along $\operatorname{Spec}$ of $R \to A$, the pullback of $M$ along the first projection, and the presheaf of $A$-modules $U \mapsto \Gamma(M_A, U)$ with its $A$-structure coming from the second projection $X_A \to \operatorname{Spec} A$ and the usual restriction maps; let $\mathcal U_A$ be the cover of $X_A$ with the same index type and opens the preimages of the $U_i$ under the first projection. Then the alternating sum $\sum_{i < \#\iota} (-1)^i \dim_A \check H^i(\mathcal U_A, M_A)$, where the $\dim_A$ are the $A$-ranks of the groups `H0` and `HSucc` of the ordered Čech complex, equals $\chi_0$.
--
--   This is the constancy of the Euler characteristic of the fibres in a proper flat family over a local base (EGA III 7.9.4; Mumford, Abelian Varieties §5), here in the form of the ordered Čech Euler characteristic computed on the literal base-changed affine covers, the quantity being independent of the field-valued point of $\operatorname{Spec} R$. It is used to compare generic and special fibres of an abelian scheme over a discrete valuation ring and to propagate triviality of kernels from field-valued fibres to the local base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_eulerChar_baseChange_eq_of_locallyTrivial_of_isLocalRing.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.OModulePresheaf.exists_forall_eulerChar_baseChange_eq_of_locallyTrivial_of_isLocalRing
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {X : Scheme.{u}} (π : X ⟶ Spec (.of R))
    [IsProper π] [Flat π] (M : X.Modules)
    (htriv : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (𝒰 : X.OrderedAffineCover) :
    ∃ χ₀ : ℤ, ∀ (A : Type u) [Field A] [Algebra R A],
      (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback
            (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).eulerChar (𝒰.baseChange π A)
        = χ₀ := by sorry
