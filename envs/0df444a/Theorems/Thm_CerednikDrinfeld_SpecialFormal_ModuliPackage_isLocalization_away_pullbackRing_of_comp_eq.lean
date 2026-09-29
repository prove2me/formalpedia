-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_isLocalization_away_pullbackRing_of_comp_eq
-- name    : CerednikDrinfeld.SpecialFormal.ModuliPackage.isLocalization_away_pullbackRing_of_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/ee55e5ae-d976-522b-b3f7-9fb58dc018c4
-- title:
--   Localisation commutes with fibre products of rings
-- statement:
--   Let $B,B',B''$ be commutative rings and $\varphi'\colon B'\to B$, $\varphi''\colon B''\to B$ ring homomorphisms, and let `ModuliPackage.pullbackRing` $\varphi'\,\varphi''$ denote the fibre product $P$, realised as the subring of $B'\times B''$ on which $\varphi'\circ\mathrm{pr}_1$ and $\varphi''\circ\mathrm{pr}_2$ agree, with `pullbackFst`, `pullbackSnd` the two component projections $P\to B'$, $P\to B''$. Fix $g\in P$, with components $g'=g.1.1$ and $g''=g.1.2$. Let further commutative rings $B_1,B'_1,B''_1$ be given, algebras over $B,B',B''$ respectively, such that $B_1$ is a localisation of $B$ away from $\varphi'(g')$, $B'_1$ a localisation of $B'$ away from $g'$, and $B''_1$ a localisation of $B''$ away from $g''$. Let $\varphi'_1\colon B'_1\to B_1$ and $\varphi''_1\colon B''_1\to B_1$ be ring maps compatible with $\varphi'$ and $\varphi''$ through the structure maps, and let $\delta\colon P\to \mathrm{pullbackRing}\,\varphi'_1\,\varphi''_1$ be a ring homomorphism whose two components are the structure maps $B'\to B'_1$ and $B''\to B''_1$ composed with `pullbackFst` $\varphi'\,\varphi''$, respectively `pullbackSnd` $\varphi'\,\varphi''$. The conclusion is a conjunction: first, $\mathrm{pullbackRing}\,\varphi'_1\,\varphi''_1$, viewed as a $P$-algebra via $\delta$, is a localisation of $P$ away from $g$; second, $\varphi'_1$ is surjective if $\varphi'$ is, and likewise for $\varphi''_1$ and $\varphi''$; third, the kernel of $\varphi'_1$ is nilpotent if that of $\varphi'$ is, and likewise for $\varphi''_1$ and $\varphi''$.
--
--   This is the statement that localisation commutes with fibre products of rings, i.e. that a basic open of $\operatorname{Spec}(B'\times_B B'')$ is the fibre product of the corresponding basic opens, stated for arbitrary localisation models and for an abstract comparison map $\delta$ pinned down by its two components, together with the persistence of surjectivity and of nilpotence of the kernel of the two legs. In this development it supplies the local models used in the Zariski-gluing arguments for the deformation functors attached to special formal modules, and in the construction of pullback–pushout squares of affine schemes with flat, surjective and nilpotent-kernel legs.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_isLocalization_away_pullbackRing_of_comp_eq.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_ModuliPackageDescent
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.SpecialFormal.ModuliPackage.isLocalization_away_pullbackRing_of_comp_eq
    {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B) (g : ModuliPackage.pullbackRing φ' φ'')
    (B₁ B'₁ B''₁ : Type) [CommRing B₁] [CommRing B'₁] [CommRing B''₁]
    [Algebra B B₁] [Algebra B' B'₁] [Algebra B'' B''₁]
    [IsLocalization.Away (φ' g.1.1) B₁] [IsLocalization.Away g.1.1 B'₁] [IsLocalization.Away g.1.2 B''₁]
    (φ'₁ : B'₁ →+* B₁) (φ''₁ : B''₁ →+* B₁)
    (hφ'₁ : φ'₁.comp (algebraMap B' B'₁) = (algebraMap B B₁).comp φ')
    (hφ''₁ : φ''₁.comp (algebraMap B'' B''₁) = (algebraMap B B₁).comp φ'')
    (δ : ModuliPackage.pullbackRing φ' φ'' →+* ModuliPackage.pullbackRing φ'₁ φ''₁)
    (hδ₁ : (ModuliPackage.pullbackFst φ'₁ φ''₁).comp δ =
      (algebraMap B' B'₁).comp (ModuliPackage.pullbackFst φ' φ''))
    (hδ₂ : (ModuliPackage.pullbackSnd φ'₁ φ''₁).comp δ =
      (algebraMap B'' B''₁).comp (ModuliPackage.pullbackSnd φ' φ'')) :
    @IsLocalization.Away (ModuliPackage.pullbackRing φ' φ'') _ g (ModuliPackage.pullbackRing φ'₁ φ''₁) _
      δ.toAlgebra ∧
    (Function.Surjective φ' → Function.Surjective φ'₁) ∧
    (Function.Surjective φ'' → Function.Surjective φ''₁) ∧
    (IsNilpotent (RingHom.ker φ') → IsNilpotent (RingHom.ker φ'₁)) ∧
    (IsNilpotent (RingHom.ker φ'') → IsNilpotent (RingHom.ker φ''₁)) := by sorry
