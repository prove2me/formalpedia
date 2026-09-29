-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing
-- name    : AlgebraicGeometry.exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/bc953c42-7bfe-5a27-b7c2-596b8df7d359
-- title:
--   Gluing schemes along two nilpotent base thickenings
-- statement:
--   Let $B$, $B'$, $B''$ be commutative rings and let $\varphi' : B' \to B$ and $\varphi'' : B'' \to B$ be surjective ring homomorphisms whose kernels are nilpotent ideals. Write $P$ for `pullbackRing` $\varphi'\,\varphi''$, the subring $\{(b',b'') \in B' \times B'' : \varphi'(b') = \varphi''(b'')\}$ of $B' \times B''$, with the two projections `pullbackFst` and `pullbackSnd` to $B'$ and $B''$. Let $f' : X' \to \operatorname{Spec} B'$, $f'' : X'' \to \operatorname{Spec} B''$ and $f_Z : Z \to \operatorname{Spec} B$ be morphisms of schemes (in the bottom universe), and let $h' : Z \to X'$, $h'' : Z \to X''$ be morphisms such that the squares with sides $h', f_Z, f', \operatorname{Spec}\varphi'$ and $h'', f_Z, f'', \operatorname{Spec}\varphi''$ are cartesian, i.e. $Z$ identifies both with $X' \times_{\operatorname{Spec} B'} \operatorname{Spec} B$ and with $X'' \times_{\operatorname{Spec} B''} \operatorname{Spec} B$. The assertion is that there exist a scheme $X$, a morphism $f : X \to \operatorname{Spec} P$ and morphisms $k' : X' \to X$, $k'' : X'' \to X$ such that the squares $(k', f', f, \operatorname{Spec}(\mathrm{fst}))$ and $(k'', f'', f, \operatorname{Spec}(\mathrm{snd}))$ are cartesian, $h' \,$ followed by $k'$ equals $h''$ followed by $k''$, the resulting square $(h', h'', k', k'')$ is a pushout of schemes, and moreover: if $f'$ and $f''$ are flat then so is $f$, and if in addition $f'$ and $f''$ are locally of finite presentation then so is $f$.
--
--   This is the gluing (pinching) of schemes along a pair of nilpotent thickenings of a common base: data over $B'$ and over $B''$ with identified restrictions to $B$ descend to a scheme over the fibre product $B' \times_B B''$, the two comparison squares remaining cartesian, the glued scheme being the pushout, and flatness and local finite presentation being inherited. It is used in the deformation-theoretic analysis of the Čerednik–Drinfel'd moduli packages, where it supplies the representing object over a fibre product of Artinian-type bases; the construction is invoked by [`AlgebraicGeometry.exists_isPushout_isPullback_specMap_pullbackFst_pullbackSnd_of_surjective_of_isNilpotent`](thm.html#AlgebraicGeometry.exists_isPushout_isPullback_specMap_pullbackFst_pullbackSnd_of_surjective_of_isNilpotent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.lean

import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CerednikDrinfeld.SpecialFormal.ModuliPackage

theorem AlgebraicGeometry.exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing
    {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B)
    (hφ's : Function.Surjective φ') (hφ''s : Function.Surjective φ'')
    (hφ'n : IsNilpotent (RingHom.ker φ')) (hφ''n : IsNilpotent (RingHom.ker φ''))
    {X' X'' Z : Scheme.{0}} (f' : X' ⟶ Spec (CommRingCat.of B')) (f'' : X'' ⟶ Spec (CommRingCat.of B''))
    (fZ : Z ⟶ Spec (CommRingCat.of B))
    (h' : Z ⟶ X') (hh' : IsPullback h' fZ f' (Spec.map (CommRingCat.ofHom φ')))
    (h'' : Z ⟶ X'') (hh'' : IsPullback h'' fZ f'' (Spec.map (CommRingCat.ofHom φ''))) :
    ∃ (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) (k' : X' ⟶ X) (k'' : X'' ⟶ X),
      IsPullback k' f' f (Spec.map (CommRingCat.ofHom (pullbackFst φ' φ''))) ∧
      IsPullback k'' f'' f (Spec.map (CommRingCat.ofHom (pullbackSnd φ' φ''))) ∧
      h' ≫ k' = h'' ≫ k'' ∧ IsPushout h' h'' k' k'' ∧
      (Flat f' → Flat f'' → Flat f) ∧
      (Flat f' → Flat f'' → LocallyOfFinitePresentation f' → LocallyOfFinitePresentation f'' →
        LocallyOfFinitePresentation f) := by sorry
