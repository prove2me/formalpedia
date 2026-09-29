-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_subsingleton_iso_map_pullback_rigSection_comp_eq
-- name    : AlgebraicGeometry.RelPicard.RigidifiedLineBundle.subsingleton_iso_map_pullback_rigSection_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/446fc7e5-8a4a-5085-b1d5-428c655a0127
-- title:
--   Rigidity: at most one rigidification-compatible isomorphism
-- statement:
--   Fix a commutative ring $R$ of universe $u$, a scheme $C$ and a morphism $c : C \to \operatorname{Spec} R$, together with $\varepsilon$, an element of `SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c`, that is, a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity (a section of $c$). Assume the hypothesis `hH0`: for every commutative $R$-algebra $A$ the structure map $A \to \Gamma(C \times_{\operatorname{Spec} R} \operatorname{Spec} A, \top)$ — the algebra structure being the one induced on global sections by the second projection — is bijective. Let $t : T \to \operatorname{Spec} R$ be a further scheme over $R$, and let $M, M'$ be rigidified line bundles for $(c,\varepsilon)$ over $t$, each consisting of a module $L$ on the fibre product $C \times_{\operatorname{Spec} R} T$ which is invertible (every point has an open neighbourhood on which the restriction of $L$ is isomorphic to the unit sheaf of modules) and whose pullback along the induced section $\varepsilon_T =$ `rigSection c t ε`, the morphism $T \to C \times_{\operatorname{Spec} R} T$ with components $t \circ \varepsilon$ and $\mathrm{id}_T$, admits some isomorphism to the unit sheaf on $T$. Let $\alpha$ and $\alpha'$ be chosen such isomorphisms $\varepsilon_T^* M.L \cong \mathcal{O}_T$ and $\varepsilon_T^* M'.L \cong \mathcal{O}_T$. Then the type of pairs consisting of an isomorphism $\varphi : M.L \cong M'.L$ of modules on $C \times_{\operatorname{Spec} R} T$ together with a proof that $\varepsilon_T^*\varphi$ followed by $\alpha'$ equals $\alpha$ is a subsingleton: any two such $\varphi$ coincide.
--
--   This is the uniqueness half of the rigidity statement for rigidified line bundles on a relative curve with a section (as in Bosch–Lütkebohmert–Raynaud, Néron Models 8.1, Proposition 4), packaged as a `Subsingleton` assertion in exactly the shape used when gluing or descending rigidified line bundles. It is invoked in the construction of descents along finite faithfully flat and along affine flat surjective morphisms, and in the gluing of rigidified line bundles along an open cover.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_subsingleton_iso_map_pullback_rigSection_comp_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.RigidifiedLineBundle.subsingleton_iso_map_pullback_rigSection_comp_eq
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M M' : RigidifiedLineBundle c ε t)
    (α : (Scheme.Modules.pullback (rigSection c t ε)).obj M.L ≅ SheafOfModules.unit T.ringCatSheaf)
    (α' : (Scheme.Modules.pullback (rigSection c t ε)).obj M'.L ≅ SheafOfModules.unit T.ringCatSheaf) :
    Subsingleton {φ : M.L ≅ M'.L // (Scheme.Modules.pullback (rigSection c t ε)).mapIso φ ≪≫ α' = α} := by sorry
