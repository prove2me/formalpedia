-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_pullback_iso_comp_eq_comp_of_isIso_of_pullback_pol_iso
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.exists_fg_subalgebra_abelianScheme_pullback_iso_comp_eq_comp_of_isIso_of_pullback_pol_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/5f023758-dc8f-5027-a0fb-8c71a7afaaa8
-- title:
--   Spreading out an abelian variety with a σ-invariant invertible module
-- statement:
--   Let $g,d,n$ be natural numbers, $k$ a field, and $u$ a linearly polarised abelian variety over $k$ in the sense of `PolarisedAbelianScheme g d n k`: a scheme $u.A$ with a structure morphism $u.f : u.A \to \operatorname{Spec} k$ which is smooth, proper, has connected fibres and admits a relative group law, a commutative relative group law $u.L$ on $T$-points, fibres of topological Krull dimension $g$, a family $u.P$ of $2g$ sections that are $n$-torsion and, over algebraically closed fields, freely generate the $n$-torsion, and an invertible module $u.pol$ giving a closed immersion by sections with geometric fibre $H^0$ of rank $d$. Let $\sigma$ be a morphism $u.A \to u.A$ over $\operatorname{Spec} k$ whose underlying morphism is an isomorphism and which is a homomorphism for $u.L$ on $T$-points (composition with $\sigma$ commutes with $u.L.mul$), and assume that every point of $\operatorname{Spec} k$ has an open neighbourhood $U$ with $\sigma^{*}u.pol$ and $u.pol$ isomorphic after restriction to $u.f^{-1}U$. Then there exist a finitely generated $\mathbb{Z}$-subalgebra $R \subseteq k$, a scheme $A_0$ with $f_0 : A_0 \to \operatorname{Spec} R$ satisfying the same bundle of properties (smooth, proper, connected fibres, a relative group law exists) together with the predicate `GeometricallyConnected`, a relative group law $L_0$ over $R$, an invertible $A_0$-module $M_0$, a morphism $\sigma_0 : A_0 \to A_0$ over $\operatorname{Spec} R$ whose underlying morphism is an isomorphism and which is a homomorphism for $L_0$ on points, such that every point of $\operatorname{Spec} R$ has an open neighbourhood $U$ with $\sigma_0^{*}M_0 \cong M_0$ after restriction to $f_0^{-1}U$, and a morphism $g_A : u.A \to A_0$ making the square formed by $g_A$, $u.f$, $f_0$ and $\operatorname{Spec}$ of the inclusion $R \hookrightarrow k$ cartesian, with: $g_A$ compatible with the group laws (composing $u.L.mul\,t\,x\,y$ with $g_A$ agrees with $L_0.mul$ over $t$ followed by $\operatorname{Spec}$ of the inclusion, applied to the composites of $x$ and $y$ with $g_A$), $g_A^{*}M_0 \cong u.pol$, and $\sigma$ followed by $g_A$ equal to $g_A$ followed by $\sigma_0$. The conclusion asserts nothing about the sections $u.P$, the fibre dimension $g$, the invariants $d$ and $n$, or relative very ampleness of $M_0$; it is therefore weaker than descending the whole polarised abelian scheme datum.
--
--   This is a spreading-out statement in the style of the limit arguments of EGA IV §8: an abelian variety over a field, equipped with an invertible module and an automorphism preserving that module locally on the base, descends to a finitely generated $\mathbb{Z}$-subalgebra together with the automorphism and the module class. It is used by the companion result which additionally spreads out the closed-immersion presentation of the polarisation, so producing a polarised abelian scheme over a finitely generated base; the proof here cites the corresponding statement without the $\sigma$-invariance hypothesis together with a direct-limit descent result for isomorphism classes of invertible modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_pullback_iso_comp_eq_comp_of_isIso_of_pullback_pol_iso.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.PolarisedAbelianScheme

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_fg_subalgebra_abelianScheme_pullback_iso_comp_eq_comp_of_isIso_of_pullback_pol_iso
    {g d n : ℕ} {k : Type} [Field k] (u : PolarisedAbelianScheme g d n k)
    (σ : SchemeHomOver u.f u.f) (hσiso : IsIso σ.1)
    (hσ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t u.f),
      NeronModelInfra.schemeHomOverComp (u.L.mul t x y) σ =
        u.L.mul t (NeronModelInfra.schemeHomOverComp x σ) (NeronModelInfra.schemeHomOverComp y σ))
    (hpol : ∀ s : ↥(Spec (CommRingCat.of k)), ∃ U : (Spec (CommRingCat.of k)).Opens, s ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (u.f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback σ.1).obj u.pol) ≅
        (Scheme.Modules.pullback (u.f ⁻¹ᵁ U).ι).obj u.pol)) :
    ∃ (R : Subalgebra ℤ k) (_ : R.FG)
      (A₀ : Scheme.{0}) (f₀ : A₀ ⟶ Spec (CommRingCat.of ↥R)) (L₀ : RelativeGroupLaw ↥R f₀)
      (_ : AbelianSchemePropertyBundle ↥R f₀)
      (_ : GeometricallyConnected f₀)
      (M₀ : A₀.Modules) (_ : Scheme.Modules.IsInvertible M₀)
      (σ₀ : SchemeHomOver f₀ f₀) (_ : IsIso σ₀.1)
      (_ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥R)) (x y : SchemeHomOver t f₀),
        NeronModelInfra.schemeHomOverComp (L₀.mul t x y) σ₀ =
          L₀.mul t (NeronModelInfra.schemeHomOverComp x σ₀) (NeronModelInfra.schemeHomOverComp y σ₀))
      (_ : ∀ s : ↥(Spec (CommRingCat.of ↥R)), ∃ U : (Spec (CommRingCat.of ↥R)).Opens, s ∈ U ∧
        Nonempty ((Scheme.Modules.pullback (f₀ ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback σ₀.1).obj M₀) ≅
          (Scheme.Modules.pullback (f₀ ⁻¹ᵁ U).ι).obj M₀))
      (gA : u.A ⟶ A₀) (hg : CategoryTheory.IsPullback gA u.f f₀ (Spec.map (CommRingCat.ofHom R.val.toRingHom))),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t u.f),
        (u.L.mul t x y).1 ≫ gA =
          (L₀.mul (t ≫ Spec.map (CommRingCat.ofHom R.val.toRingHom))
            ⟨x.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
            ⟨y.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1) ∧
      Nonempty ((Scheme.Modules.pullback gA).obj M₀ ≅ u.pol) ∧
      σ.1 ≫ gA = gA ≫ σ₀.1 := by sorry
