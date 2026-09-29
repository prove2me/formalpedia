-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isClosedImmersion_forall_iff_locallyIsoOver_unit_of_flat_of_isProper
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isClosedImmersion_forall_iff_locallyIsoOver_unit_of_flat_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/d48b156f-62e6-539e-8769-4034bcec1744
-- title:
--   See-saw theorem: trivialisation locus is a closed subscheme
-- statement:
--   Let $R$ be a commutative ring and $c : X \to \operatorname{Spec} R$ a proper flat morphism of schemes, and assume that for every commutative $R$-algebra $B$ the ring map on global sections induced by the projection $X \times_{\operatorname{Spec} R} \operatorname{Spec} B \to \operatorname{Spec} B$ is bijective. Let $T$ be a locally Noetherian scheme with a morphism $t : T \to \operatorname{Spec} R$, and let $N$, $N_{\mathrm{inv}}$ be modules on $X \times_{\operatorname{Spec} R} T$ that are invertible in the sense that every point has an open neighbourhood $U$ over which the pullback along $U \hookrightarrow X \times_{\operatorname{Spec} R} T$ is isomorphic to the unit module. Assume: (i) for every field $K$ and every morphism $k : \operatorname{Spec} K \to T$, if the pullbacks of $N$ and of $N_{\mathrm{inv}}$ along the first projection $(X \times_{\operatorname{Spec} R} T) \times_T \operatorname{Spec} K \to X \times_{\operatorname{Spec} R} T$ both admit a non-zero global section, then the pullback of $N$ is isomorphic to the unit module there; and (ii) for every scheme $Y$ and morphism $g : Y \to X \times_{\operatorname{Spec} R} T$, triviality of $g^* N$ implies triviality of $g^* N_{\mathrm{inv}}$. Then there are a scheme $Z$ and a closed immersion $\iota : Z \to T$ such that for every scheme $T'$ and morphism $\psi : T' \to T$, $\psi$ factors as $z$ followed by $\iota$ for some $z : T' \to Z$ if and only if, for the projection $(X \times_{\operatorname{Spec} R} T) \times_T T' \to T'$, every point of $T'$ has an open neighbourhood $V$ over whose preimage the pullback of $N$ and the unit module become isomorphic. Uniqueness of $Z$ is not asserted.
--
--   This is the single-bundle form of Mumford's see-saw theorem over a locally Noetherian base: the locus in $T$ over which an invertible module on $X \times_{\operatorname{Spec} R} T$ is trivial locally over the base is cut out by a closed immersion. It is the base-change-patched global version of the affine-base statement [`AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_ideal_forall_iff_locallyIsoOver_unit_of_flat_of_isProper`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_ideal_forall_iff_locallyIsoOver_unit_of_flat_of_isProper), and is used to obtain the two-bundle form [`AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isClosedImmersion_forall_iff_locallyIsoOver_of_flat_of_isProper`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isClosedImmersion_forall_iff_locallyIsoOver_of_flat_of_isProper), from which the closed subgroup schemes attached to line bundles on abelian schemes are built.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isClosedImmersion_forall_iff_locallyIsoOver_unit_of_flat_of_isProper.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isClosedImmersion_forall_iff_locallyIsoOver_unit_of_flat_of_isProper
    {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of R)) [IsProper c] [Flat c]
    (hH0 : ∀ (B : Type u) [CommRing B] [Algebra R B],
      Function.Bijective (Limits.pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap R B)))).appTop)
    {T : Scheme.{u}} [IsLocallyNoetherian T] (t : T ⟶ Spec (CommRingCat.of R))
    (N Ninv : (Limits.pullback c t).Modules)
    (hN : Scheme.Modules.IsInvertible N) (hNinv : Scheme.Modules.IsInvertible Ninv)
    (hfib : ∀ (K : Type u) [Field K] (k : Spec (CommRingCat.of K) ⟶ T),
      (∃ s : Γ((Scheme.Modules.pullback (Limits.pullback.fst (Limits.pullback.snd c t) k)).obj N, ⊤), s ≠ 0) →
      (∃ s' : Γ((Scheme.Modules.pullback (Limits.pullback.fst (Limits.pullback.snd c t) k)).obj Ninv, ⊤), s' ≠ 0) →
        Nonempty ((Scheme.Modules.pullback (Limits.pullback.fst (Limits.pullback.snd c t) k)).obj N ≅
          SheafOfModules.unit (Limits.pullback (Limits.pullback.snd c t) k).ringCatSheaf))
    (hinv : ∀ (Y : Scheme.{u}) (g : Y ⟶ Limits.pullback c t),
      Nonempty ((Scheme.Modules.pullback g).obj N ≅ SheafOfModules.unit Y.ringCatSheaf) →
        Nonempty ((Scheme.Modules.pullback g).obj Ninv ≅ SheafOfModules.unit Y.ringCatSheaf)) :
    ∃ (Z : Scheme.{u}) (ι : Z ⟶ T), IsClosedImmersion ι ∧
      ∀ {T' : Scheme.{u}} (ψ : T' ⟶ T),
        (∃ z : T' ⟶ Z, z ≫ ι = ψ) ↔
          Scheme.Modules.LocallyIsoOver (Limits.pullback.snd (Limits.pullback.snd c t) ψ)
            ((Scheme.Modules.pullback (Limits.pullback.fst (Limits.pullback.snd c t) ψ)).obj N)
            (SheafOfModules.unit (Limits.pullback (Limits.pullback.snd c t) ψ).ringCatSheaf) := by sorry
