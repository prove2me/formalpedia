-- Prove2me | Theorems.Thm_AlgebraicGeometry_isPushout_pullbackMap_of_isPushout_of_isPushout_of_flat
-- name    : AlgebraicGeometry.isPushout_pullbackMap_of_isPushout_of_isPushout_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/f44889ad-74a1-5994-b08d-e0fa9a198cc6
-- title:
--   Fibre products of flat glued schemes are push-outs
-- statement:
--   Let $B$, $B'$, $B''$ be commutative rings and let $\varphi' : B' \to B$, $\varphi'' : B'' \to B$ be surjective ring homomorphisms whose kernels are nilpotent ideals. Write $P =$ `pullbackRing φ' φ''` for the subring of $B' \times B''$ on which $\varphi' \circ \mathrm{pr}_1$ and $\varphi'' \circ \mathrm{pr}_2$ agree, i.e. the fibre product $B' \times_B B''$, with the two projections `pullbackFst φ' φ''` to $B'$ and `pullbackSnd φ' φ''` to $B''$. Suppose given schemes $X, X', X'', X_Z$ together with a flat morphism $f_X : X \to \operatorname{Spec} P$ and morphisms $f_{X'} : X' \to \operatorname{Spec} B'$, $f_{X''} : X'' \to \operatorname{Spec} B''$, $f_{X_Z} : X_Z \to \operatorname{Spec} B$, and morphisms $h'_X : X_Z \to X'$, $h''_X : X_Z \to X''$, $k'_X : X' \to X$, $k''_X : X'' \to X$ such that $h'_X$ (resp. $h''_X$) exhibits $X_Z$ as the base change of $f_{X'}$ along $\operatorname{Spec}$ of $\varphi'$ (resp. of $f_{X''}$ along $\varphi''$), $k'_X$ (resp. $k''_X$) exhibits $X'$ (resp. $X''$) as the base change of $f_X$ along $\operatorname{Spec}$ of `pullbackFst φ' φ''` (resp. `pullbackSnd φ' φ''`), and such that the square $(h'_X, h''_X, k'_X, k''_X)$ is a push-out; and let $f_Y : Y \to \operatorname{Spec} P$ flat, $Y', Y'', Y_Z$ and morphisms $h'_Y, h''_Y, k'_Y, k''_Y$ satisfy the same conditions. The conclusion is threefold: the square formed by the maps induced on fibre products, $X_Z \times_{\operatorname{Spec} B} Y_Z \to X' \times_{\operatorname{Spec} B'} Y'$ and $X_Z \times_{\operatorname{Spec} B} Y_Z \to X'' \times_{\operatorname{Spec} B''} Y''$, followed by the induced maps into $X \times_{\operatorname{Spec} P} Y$, is a push-out; and each of the two squares expressing $X' \times_{\operatorname{Spec} B'} Y'$ and $X'' \times_{\operatorname{Spec} B''} Y''$, with their structure morphisms to $\operatorname{Spec} B'$ and $\operatorname{Spec} B''$, as the base change of $X \times_{\operatorname{Spec} P} Y \to \operatorname{Spec} P$ along $\operatorname{Spec}$ of `pullbackFst φ' φ''`, resp. `pullbackSnd φ' φ''`, is cartesian.
--
--   This is the compatibility of gluing along a nilpotent thickening with fibre products: the equivalence between flat objects over $B' \times_B B''$ and flat glued triples respects products, so a fibre product of two glued flat schemes is again glued from the fibre products of the pieces. It is used in the Čerednik–Drinfeld part of the development, where group laws and multiplication maps on fake elliptic curves over $\operatorname{Spec}(B' \times_B B'')$ are produced by descending data from the two pieces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isPushout_pullbackMap_of_isPushout_of_isPushout_of_flat.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CerednikDrinfeld.SpecialFormal.ModuliPackage
open AlgebraicGeometry

theorem AlgebraicGeometry.isPushout_pullbackMap_of_isPushout_of_isPushout_of_flat
    {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B)
    (hφ's : Function.Surjective φ') (hφ''s : Function.Surjective φ'')
    (hφ'n : IsNilpotent (RingHom.ker φ')) (hφ''n : IsNilpotent (RingHom.ker φ''))

    {X X' X'' XZ : Scheme.{0}}
    (fX : X ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) [Flat fX]
    (fX' : X' ⟶ Spec (CommRingCat.of B')) (fX'' : X'' ⟶ Spec (CommRingCat.of B'')) (fXZ : XZ ⟶ Spec (CommRingCat.of B))
    (hX' : XZ ⟶ X') (cXh' : IsPullback hX' fXZ fX' (Spec.map (CommRingCat.ofHom φ')))
    (hX'' : XZ ⟶ X'') (cXh'' : IsPullback hX'' fXZ fX'' (Spec.map (CommRingCat.ofHom φ'')))
    (kX' : X' ⟶ X) (cXk' : IsPullback kX' fX' fX (Spec.map (CommRingCat.ofHom (pullbackFst φ' φ''))))
    (kX'' : X'' ⟶ X) (cXk'' : IsPullback kX'' fX'' fX (Spec.map (CommRingCat.ofHom (pullbackSnd φ' φ''))))
    (poX : IsPushout hX' hX'' kX' kX'')

    {Y Y' Y'' YZ : Scheme.{0}}
    (fY : Y ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) [Flat fY]
    (fY' : Y' ⟶ Spec (CommRingCat.of B')) (fY'' : Y'' ⟶ Spec (CommRingCat.of B'')) (fYZ : YZ ⟶ Spec (CommRingCat.of B))
    (hY' : YZ ⟶ Y') (cYh' : IsPullback hY' fYZ fY' (Spec.map (CommRingCat.ofHom φ')))
    (hY'' : YZ ⟶ Y'') (cYh'' : IsPullback hY'' fYZ fY'' (Spec.map (CommRingCat.ofHom φ'')))
    (kY' : Y' ⟶ Y) (cYk' : IsPullback kY' fY' fY (Spec.map (CommRingCat.ofHom (pullbackFst φ' φ''))))
    (kY'' : Y'' ⟶ Y) (cYk'' : IsPullback kY'' fY'' fY (Spec.map (CommRingCat.ofHom (pullbackSnd φ' φ''))))
    (poY : IsPushout hY' hY'' kY' kY'') :
    IsPushout
      (pullback.map fXZ fYZ fX' fY' hX' hY' (Spec.map (CommRingCat.ofHom φ')) cXh'.w.symm cYh'.w.symm)
      (pullback.map fXZ fYZ fX'' fY'' hX'' hY'' (Spec.map (CommRingCat.ofHom φ'')) cXh''.w.symm cYh''.w.symm)
      (pullback.map fX' fY' fX fY kX' kY' (Spec.map (CommRingCat.ofHom (pullbackFst φ' φ''))) cXk'.w.symm cYk'.w.symm)
      (pullback.map fX'' fY'' fX fY kX'' kY'' (Spec.map (CommRingCat.ofHom (pullbackSnd φ' φ''))) cXk''.w.symm cYk''.w.symm) ∧
    IsPullback (pullback.map fX' fY' fX fY kX' kY' (Spec.map (CommRingCat.ofHom (pullbackFst φ' φ''))) cXk'.w.symm cYk'.w.symm)
      (pullback.fst fX' fY' ≫ fX') (pullback.fst fX fY ≫ fX) (Spec.map (CommRingCat.ofHom (pullbackFst φ' φ''))) ∧
    IsPullback (pullback.map fX'' fY'' fX fY kX'' kY'' (Spec.map (CommRingCat.ofHom (pullbackSnd φ' φ''))) cXk''.w.symm cYk''.w.symm)
      (pullback.fst fX'' fY'' ≫ fX'') (pullback.fst fX fY ≫ fX) (Spec.map (CommRingCat.ofHom (pullbackSnd φ' φ''))) := by sorry
