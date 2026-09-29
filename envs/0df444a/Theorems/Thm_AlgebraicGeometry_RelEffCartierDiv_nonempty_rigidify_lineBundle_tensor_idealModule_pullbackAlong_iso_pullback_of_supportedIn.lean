-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_nonempty_rigidify_lineBundle_tensor_idealModule_pullbackAlong_iso_pullback_of_supportedIn
-- name    : AlgebraicGeometry.RelEffCartierDiv.nonempty_rigidify_lineBundle_tensor_idealModule_pullbackAlong_iso_pullback_of_supportedIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/027f2442-297a-5e20-a0ba-6de1cf4a7088
-- title:
--   Rigidified 𝒪(D-E_T) commutes with base change
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme and $c : C \to \operatorname{Spec} R$ a separated morphism, and let $\varepsilon$ be a section of $c$, i.e. a morphism $\operatorname{Spec} R \to C$ with $\varepsilon \circ$ composed into $c$ the identity. Let $U \subseteq C$ be an open subscheme whose structure morphism $U \hookrightarrow C$ followed by $c$ is smooth of relative dimension $1$. Let $E$ be a relative effective Cartier divisor of degree $\rho$ for $c$ over the identity of $\operatorname{Spec} R$ — that is, a quasi-coherent ideal on $C \times_R \operatorname{Spec} R$ whose closed subscheme is finite, flat and locally of finite presentation over the base with fibre rank $\rho$ everywhere — whose support is contained in the preimage of $U$ under the first projection. Let $r : \mathbb N$, let $t : T \to \operatorname{Spec} R$ and $t' : T' \to \operatorname{Spec} R$ be $R$-schemes, let $\psi : T' \to T$ satisfy $\psi$ followed by $t$ equals $t'$, and let $D$ be a relative effective Cartier divisor of degree $r$ for $c$ over $t$, again supported in the preimage of $U$. Write $\Psi = 1_C \times \psi : C \times_R T' \to C \times_R T$ for the induced map of products, $\varepsilon_T : T \to C \times_R T$ for the section determined by $\varepsilon$, and for a divisor $D$ let $\mathcal O(D)$ denote the dual of its ideal module and $\mathcal I_E$ the ideal module itself (the kernel of the comparison of the structure sheaf with the pushforward from the closed subscheme); rigidification of an $L$ on $C \times_R T$ means $L \otimes \mathrm{pr}_2^{*}\bigl((\varepsilon_T^{*}L)^{\vee}\bigr)$. Then there exists an isomorphism of sheaves of modules on $C \times_R T'$ between the rigidification of $\mathcal O(\psi^{*}D) \otimes \mathcal I_{E_{T'}}$ and the pullback along $\Psi$ of the rigidification of $\mathcal O(D) \otimes \mathcal I_{E_{T}}$, where $\psi^{*}D$ and $E_{T}$, $E_{T'}$ denote the base changes of $D$ and $E$ obtained by comapping their ideals along the corresponding maps of products.
--
--   This is the base-change compatibility of the canonically rigidified line bundle $\mathcal O(D - E_T)$ attached to a relative effective Cartier divisor supported in a smooth relative curve locus. It feeds the construction of open charts for the relative Picard functor of $c$ with a polarising divisor $E$, and the recovery of a divisor from an isomorphism class of its rigidified bundle.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_nonempty_rigidify_lineBundle_tensor_idealModule_pullbackAlong_iso_pullback_of_supportedIn.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_IdealSheafModuleMaps
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicCurve_RelCartier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra

theorem AlgebraicGeometry.RelEffCartierDiv.nonempty_rigidify_lineBundle_tensor_idealModule_pullbackAlong_iso_pullback_of_supportedIn
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    {ρ : ℕ} (E : RelEffCartierDiv c ρ (𝟙 (Spec (CommRingCat.of R)))) (hEU : E.SupportedIn U)
    {r : ℕ} {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) (D : RelEffCartierDiv c r t) (hDU : D.SupportedIn U) :
    Nonempty (Scheme.Modules.rigidify (RelPicard.rigSection c t' ε) (pullback.snd c t')
          ((D.pullbackAlong ψ.1 ψ.2).lineBundle ⊗ (E.pullbackAlong t' (Category.comp_id t')).idealModule) ≅
      (Scheme.Modules.pullback (RelPicard.baseChangeSnd c ψ)).obj
        (Scheme.Modules.rigidify (RelPicard.rigSection c t ε) (pullback.snd c t)
          (D.lineBundle ⊗ (E.pullbackAlong t (Category.comp_id t)).idealModule))) := by sorry
