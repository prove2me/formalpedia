-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_rigidify_lineBundle_tensor_idealModule_and_nonempty_pullback_iso_of_supportedIn
-- name    : AlgebraicGeometry.RelEffCartierDiv.isInvertible_rigidify_lineBundle_tensor_idealModule_and_nonempty_pullback_iso_of_supportedIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/3798ca17-7933-518e-afdc-b9bac1bb8504
-- title:
--   The rigidified bundle 𝒪(D-E_T) is invertible and trivial along ε
-- statement:
--   Let $R$ be a commutative ring, let $c : C \to \operatorname{Spec} R$ be a separated morphism of schemes, and let $\varepsilon$ be a morphism $\operatorname{Spec} R \to C$ with $\varepsilon \circ c$-composite equal to the identity, i.e. a section of $c$. Let $U \subseteq C$ be an open subscheme whose inclusion followed by $c$ is smooth of relative dimension $1$. Let $E$ be a relative effective Cartier divisor of degree $\rho$ for $c$ over the identity of $\operatorname{Spec} R$ — an ideal sheaf datum on $C$ whose closed subscheme is finite, flat and locally of finite presentation over the base with all fibre ranks $\rho$ — whose support is contained in $U$, and let $D$ be such a divisor of degree $r$ for $c$ over an $R$-scheme $t : T \to \operatorname{Spec} R$, an ideal sheaf datum $D.I$ on $C \times_R T$ finite, flat and locally of finite presentation over $T$ with all fibre ranks $r$, whose support is contained in the preimage of $U$ under the first projection. Write $E_T$ for the pull-back of $E$ along $t$, and $\varepsilon_T =$ `RelPicard.rigSection c t ε` for the induced morphism $T \to C \times_R T$ determined by $t$ followed by $\varepsilon$ and $\mathrm{id}_T$. Put $L = D.I^{\vee} \otimes E_{T}.I$, the tensor product of the dual of the ideal module of $D$ with the ideal module of $E_T$, and let $M = L \otimes \mathrm{pr}_2^{*}\bigl((\varepsilon_T^{*}L)^{\vee}\bigr)$ be its rigidification along $\varepsilon_T$ and $\mathrm{pr}_2$. Then $M$ is invertible, in the sense that every point of $C \times_R T$ has an open neighbourhood on which the restriction of $M$ is isomorphic to the unit module, and the set of isomorphisms $\varepsilon_T^{*}M \cong \mathbf{1}_{T.\mathrm{Modules}}$ is non-empty.
--
--   This produces the rigidified line bundle $\mathcal{O}(D - E_T)$ attached to a relative effective divisor $D$ twisted by a fixed polarisation divisor $E$, the object representing a point of the relative Picard functor of $C/\operatorname{Spec} R$ rigidified along the section $\varepsilon$. It is used in the construction of open charts for the relative Picard presheaf, in [`AlgebraicGeometry.RelPicard.exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme`](thm.html#AlgebraicGeometry.RelPicard.exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_rigidify_lineBundle_tensor_idealModule_and_nonempty_pullback_iso_of_supportedIn.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicCurve_RelCartier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra

theorem AlgebraicGeometry.RelEffCartierDiv.isInvertible_rigidify_lineBundle_tensor_idealModule_and_nonempty_pullback_iso_of_supportedIn
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    {ρ : ℕ} (E : RelEffCartierDiv c ρ (𝟙 (Spec (CommRingCat.of R)))) (hEU : E.SupportedIn U)
    {r : ℕ} {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (D : RelEffCartierDiv c r t)
    (hD : D.SupportedIn U) :
    Scheme.Modules.IsInvertible
        (Scheme.Modules.rigidify (RelPicard.rigSection c t ε) (pullback.snd c t)
          (D.lineBundle ⊗ (E.pullbackAlong t (Category.comp_id t)).idealModule)) ∧
      Nonempty ((Scheme.Modules.pullback (RelPicard.rigSection c t ε)).obj
          (Scheme.Modules.rigidify (RelPicard.rigSection c t ε) (pullback.snd c t)
            (D.lineBundle ⊗ (E.pullbackAlong t (Category.comp_id t)).idealModule)) ≅ 𝟙_ T.Modules) := by sorry
