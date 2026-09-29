-- Prove2me | Theorems.Thm_AlgebraicGeometry_isPullback_isPushout_specMap_of_isPullback_pullbackRing_of_isPushout_of_surjective_of_isNilpotent
-- name    : AlgebraicGeometry.isPullback_isPushout_specMap_of_isPullback_pullbackRing_of_isPushout_of_surjective_of_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/faa3f542-c28e-5e82-a0de-eb2f27012c60
-- title:
--   Affine chart for gluing along a nilpotent thickening
-- statement:
--   Let $B$, $B'$, $B''$ be commutative rings and let $\varphi' : B' \to B$, $\varphi'' : B'' \to B$ be surjective ring homomorphisms whose kernels are nilpotent ideals (i.e. $(\ker \varphi')^n = 0$ and $(\ker \varphi'')^m = 0$ for some $n$, $m$). Write $P =$ `pullbackRing φ' φ''` for the subring of $B' \times B''$ on which $\varphi' \circ \mathrm{fst}$ and $\varphi'' \circ \mathrm{snd}$ agree, that is, the set of pairs $(x,y)$ with $\varphi'(x) = \varphi''(y)$, with `pullbackFst` and `pullbackSnd` its two coordinate projections to $B'$ and $B''$. Let $A$, $A'$, $A''$, $A_0$ be commutative rings (objects of `CommRingCat.{0}`) with maps $a' : A \to A'$, $a'' : A \to A''$, $g' : A' \to A_0$, $g'' : A'' \to A_0$ forming a pullback square, and let $u : P \to A$, $s' : B' \to A'$, $s'' : B'' \to A''$, $s_0 : B \to A_0$ be ring maps such that `pullbackFst` followed by $s'$ equals $u$ followed by $a'$, `pullbackSnd` followed by $s''$ equals $u$ followed by $a''$, $\varphi'$ followed by $s_0$ equals $s'$ followed by $g'$, $\varphi''$ followed by $s_0$ equals $s''$ followed by $g''$, and such that the last two squares, $(\varphi', s', s_0, g')$ and $(\varphi'', s'', s_0, g'')$, are pushouts in `CommRingCat`. The conclusion is a conjunction of three assertions about schemes: $\operatorname{Spec} A'$, with the maps induced by $a'$ and $s'$, is the fibre product of $\operatorname{Spec} A \to \operatorname{Spec} P$ and $\operatorname{Spec} B' \to \operatorname{Spec} P$; likewise $\operatorname{Spec} A''$ is the fibre product of $\operatorname{Spec} A \to \operatorname{Spec} P$ and $\operatorname{Spec} B'' \to \operatorname{Spec} P$; and the square of spectra with $\operatorname{Spec} g'$, $\operatorname{Spec} g''$ out of $\operatorname{Spec} A_0$ and $\operatorname{Spec} a'$, $\operatorname{Spec} a''$ into $\operatorname{Spec} A$ is a pushout of schemes.
--
--   This is the affine chart of the gluing of schemes along a nilpotent thickening: it says that an algebra over the fibre product $B' \times_B B''$ obtained as $A' \times_{A_0} A''$ has spectrum which is simultaneously cartesian over each of the two factors and a pushout of the spectra of $A'$ and $A''$ along $\operatorname{Spec} A_0$. It is used by [`AlgebraicGeometry.exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing`](thm.html#AlgebraicGeometry.exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing) in the construction of the scheme-level gluing package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isPullback_isPushout_specMap_of_isPullback_pullbackRing_of_isPushout_of_surjective_of_isNilpotent.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CerednikDrinfeld.SpecialFormal.ModuliPackage

theorem AlgebraicGeometry.isPullback_isPushout_specMap_of_isPullback_pullbackRing_of_isPushout_of_surjective_of_isNilpotent
    {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B)
    (hφ's : Function.Surjective φ') (hφ''s : Function.Surjective φ'')
    (hφ'n : IsNilpotent (RingHom.ker φ')) (hφ''n : IsNilpotent (RingHom.ker φ''))
    {A A' A'' A₀ : CommRingCat.{0}}
    {a' : A ⟶ A'} {a'' : A ⟶ A''} {g' : A' ⟶ A₀} {g'' : A'' ⟶ A₀} (hA : IsPullback a' a'' g' g'')
    (u : CommRingCat.of ↥(pullbackRing φ' φ'') ⟶ A) (s' : CommRingCat.of B' ⟶ A') (s'' : CommRingCat.of B'' ⟶ A'')
    (s₀ : CommRingCat.of B ⟶ A₀)
    (hu' : CommRingCat.ofHom (pullbackFst φ' φ'') ≫ s' = u ≫ a')
    (hu'' : CommRingCat.ofHom (pullbackSnd φ' φ'') ≫ s'' = u ≫ a'')
    (hg' : CommRingCat.ofHom φ' ≫ s₀ = s' ≫ g') (hg'' : CommRingCat.ofHom φ'' ≫ s₀ = s'' ≫ g'')
    (hco' : IsPushout (CommRingCat.ofHom φ') s' s₀ g') (hco'' : IsPushout (CommRingCat.ofHom φ'') s'' s₀ g'') :
    IsPullback (Spec.map a') (Spec.map s') (Spec.map u) (Spec.map (CommRingCat.ofHom (pullbackFst φ' φ''))) ∧
    IsPullback (Spec.map a'') (Spec.map s'') (Spec.map u) (Spec.map (CommRingCat.ofHom (pullbackSnd φ' φ''))) ∧
    IsPushout (Spec.map g') (Spec.map g'') (Spec.map a') (Spec.map a'') := by sorry
