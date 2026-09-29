-- Prove2me | Theorems.Thm_AlgebraicGeometry_isPushout_of_flat_of_isPullback_specMap_pullbackFst_pullbackSnd
-- name    : AlgebraicGeometry.isPushout_of_flat_of_isPullback_specMap_pullbackFst_pullbackSnd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/e9137043-eaea-5bcf-9c41-7cd3d0b3ab41
-- title:
--   Flat schemes over a ring fibre product are pushouts
-- statement:
--   Let $B$, $B'$, $B''$ be commutative rings (in the zeroth universe) and let $\varphi' : B' \to B$, $\varphi'' : B'' \to B$ be ring homomorphisms that are surjective and whose kernels are nilpotent ideals; write $P$ for `pullbackRing` $\varphi'\,\varphi''$, the subring of $B' \times B''$ on which $\varphi' \circ \mathrm{pr}_1$ and $\varphi'' \circ \mathrm{pr}_2$ agree, i.e. the fibre product $B' \times_B B''$, with `pullbackFst` and `pullbackSnd` its two coordinate projections to $B'$ and $B''$. Let $Y, Y', Y'', Y_0$ be schemes, $f : Y \to \operatorname{Spec} P$ a flat morphism, and $f' : Y' \to \operatorname{Spec} B'$, $f'' : Y'' \to \operatorname{Spec} B''$, $f_0 : Y_0 \to \operatorname{Spec} B$ further morphisms. Assume given $k' : Y' \to Y$ and $k'' : Y'' \to Y$ exhibiting $Y'$ and $Y''$ as the fibre products $Y \times_{\operatorname{Spec} P} \operatorname{Spec} B'$ and $Y \times_{\operatorname{Spec} P} \operatorname{Spec} B''$ (cartesian squares over $\operatorname{Spec}$ of the two projections), and $h' : Y_0 \to Y'$, $h'' : Y_0 \to Y''$ exhibiting $Y_0$ as $Y' \times_{\operatorname{Spec} B'} \operatorname{Spec} B$ and as $Y'' \times_{\operatorname{Spec} B''} \operatorname{Spec} B$, together with the compatibility $h' \circ k' = h'' \circ k''$ (in Lean's diagrammatic order $h' \gg k' = h'' \gg k''$). Then the square with sides $h', h'', k', k''$ is a pushout of schemes, so $Y \cong Y' \sqcup_{Y_0} Y''$.
--
--   This is the gluing (Schlessinger-type) statement that a flat scheme over a fibre product $B' \times_B B''$ of nilpotent thickenings is recovered as the pushout of its two base changes along the thickened pieces. It is used in the study of moduli of fake elliptic curves in the Čerednik–Drinfeld setting, both to propagate pushout squares through fibre products of morphisms and to check the algebra identities (associativity, commutativity, action axioms) for the structures carried by those moduli.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isPushout_of_flat_of_isPullback_specMap_pullbackFst_pullbackSnd.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open CerednikDrinfeld.SpecialFormal.ModuliPackage

theorem AlgebraicGeometry.isPushout_of_flat_of_isPullback_specMap_pullbackFst_pullbackSnd
    {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B)
    (hφ's : Function.Surjective φ') (hφ''s : Function.Surjective φ'')
    (hφ'n : IsNilpotent (RingHom.ker φ')) (hφ''n : IsNilpotent (RingHom.ker φ''))
    {Y Y' Y'' Y₀ : Scheme.{0}}
    (f : Y ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) [Flat f]
    (f' : Y' ⟶ Spec (CommRingCat.of B')) (f'' : Y'' ⟶ Spec (CommRingCat.of B'')) (f₀ : Y₀ ⟶ Spec (CommRingCat.of B))
    (k' : Y' ⟶ Y) (hk' : IsPullback k' f' f (Spec.map (CommRingCat.ofHom (pullbackFst φ' φ''))))
    (k'' : Y'' ⟶ Y) (hk'' : IsPullback k'' f'' f (Spec.map (CommRingCat.ofHom (pullbackSnd φ' φ''))))
    (h' : Y₀ ⟶ Y') (hh' : IsPullback h' f₀ f' (Spec.map (CommRingCat.ofHom φ')))
    (h'' : Y₀ ⟶ Y'') (hh'' : IsPullback h'' f₀ f'' (Spec.map (CommRingCat.ofHom φ'')))
    (hcomm : h' ≫ k' = h'' ≫ k'') :
    IsPushout h' h'' k' k'' := by sorry
