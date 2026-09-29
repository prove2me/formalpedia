-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_iso_hom_comp_eq_of_isPullback_of_isPullback_of_three_le
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.iso_hom_comp_eq_of_isPullback_of_isPullback_of_three_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/a4803e0c-2025-5652-9702-e6008a491210
-- title:
--   Rigidity: overlap isomorphisms commute with base-change comparisons
-- statement:
--   Fix naturals $g,d,n$ with $3 \le n$, rings $S$, $S'$, a ring homomorphism $\varphi \colon S \to S'$ with $n$ a unit in $S'$, a polarised abelian scheme $u$ of type $(g,d,n)$ over $S$ and two such objects $v,v'$ over $S'$ (each consisting of a scheme with a structure morphism to the spectrum of the base, a commutative relative group law, smoothness, properness and connected fibres, fibres of topological Krull dimension $g$, a family of $2g$ sections $P_i$ that are $n$-torsion and give an exact basis for the $n$-torsion on geometric fibres, and an invertible module, very ample in the sense of admitting a closed immersion by sections, whose geometric fibrewise $H^0$ has rank $d$). Assume given $gA \colon v.A \to u.A$ and $gA' \colon v'.A \to u.A$, each making the square with the structure maps and $\operatorname{Spec}\varphi$ cartesian, each compatible with the group laws on $T$-points, carrying the $i$-th level section to $\operatorname{Spec}\varphi$ followed by $(u.P\,i)$, and with the pullback of $u.\mathrm{pol}$ isomorphic to the polarisation downstairs. Assume further an isomorphism $e \colon v.A \cong v'.A$ over $\operatorname{Spec} S'$, compatible with the group laws on $T$-points, with $(v.P\,i)$ followed by $e$ equal to $(v'.P\,i)$, and such that every point of $\operatorname{Spec} S'$ has an open neighbourhood $U$ over whose preimage the pullback along $e$ of $v'.\mathrm{pol}$ is isomorphic to $v.\mathrm{pol}$. Then $e$ followed by $gA'$ equals $gA$.
--
--   This is the rigidity of level-$n$ structures for $n \ge 3$ in the form needed for descent: a base change of a polarised abelian scheme with level structure admits only one comparison morphism, so any isomorphism between two such base changes is automatically the canonical one. It is used when gluing data given on a cover of the base, for instance in producing an action compatible with charts in the construction of quaternionic multiplication structures, where it removes the need for separate cocycle bookkeeping.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_iso_hom_comp_eq_of_isPullback_of_isPullback_of_three_le.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.PolarisedAbelianScheme

theorem AlgebraicGeometry.PolarisedAbelianScheme.iso_hom_comp_eq_of_isPullback_of_isPullback_of_three_le
    {g d n : ℕ} (hn : 3 ≤ n) {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') (hn' : IsUnit ((n : ℕ) : S'))
    (u : PolarisedAbelianScheme g d n S) (v v' : PolarisedAbelianScheme g d n S')

    (gA : v.A ⟶ u.A) (hgA : CategoryTheory.IsPullback gA v.f u.f (Spec.map (CommRingCat.ofHom φ)))
    (hmulA : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' v.f),
      (v.L.mul t' x y).1 ≫ gA =
        (u.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨x.1 ≫ gA, by rw [Category.assoc, hgA.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ gA, by rw [Category.assoc, hgA.w, ← Category.assoc, y.2]⟩).1)
    (hPA : ∀ i, (v.P i).1 ≫ gA = Spec.map (CommRingCat.ofHom φ) ≫ (u.P i).1)
    (hpolA : Nonempty ((Scheme.Modules.pullback gA).obj u.pol ≅ v.pol))
    (gA' : v'.A ⟶ u.A) (hgA' : CategoryTheory.IsPullback gA' v'.f u.f (Spec.map (CommRingCat.ofHom φ)))
    (hmulA' : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' v'.f),
      (v'.L.mul t' x y).1 ≫ gA' =
        (u.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨x.1 ≫ gA', by rw [Category.assoc, hgA'.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ gA', by rw [Category.assoc, hgA'.w, ← Category.assoc, y.2]⟩).1)
    (hPA' : ∀ i, (v'.P i).1 ≫ gA' = Spec.map (CommRingCat.ofHom φ) ≫ (u.P i).1)
    (hpolA' : Nonempty ((Scheme.Modules.pullback gA').obj u.pol ≅ v'.pol))

    (e : v.A ≅ v'.A) (he : e.hom ≫ v'.f = v.f)
    (emul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t v.f),
      (v.L.mul t x y).1 ≫ e.hom =
        (v'.L.mul t ⟨x.1 ≫ e.hom, by rw [Category.assoc, he]; exact x.2⟩
          ⟨y.1 ≫ e.hom, by rw [Category.assoc, he]; exact y.2⟩).1)
    (eP : ∀ i, (v.P i).1 ≫ e.hom = (v'.P i).1)
    (epol : ∀ p : ↥(Spec (CommRingCat.of S')), ∃ U : (Spec (CommRingCat.of S')).Opens, p ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (v.f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback e.hom).obj v'.pol) ≅
        (Scheme.Modules.pullback (v.f ⁻¹ᵁ U).ι).obj v.pol)) :
    e.hom ≫ gA' = gA := by sorry
