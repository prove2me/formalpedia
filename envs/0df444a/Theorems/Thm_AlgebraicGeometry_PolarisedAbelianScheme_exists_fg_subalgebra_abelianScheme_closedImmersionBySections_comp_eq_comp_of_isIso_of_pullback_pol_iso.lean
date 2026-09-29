-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_closedImmersionBySections_comp_eq_comp_of_isIso_of_pullback_pol_iso
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.exists_fg_subalgebra_abelianScheme_closedImmersionBySections_comp_eq_comp_of_isIso_of_pullback_pol_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/fade6475-e419-547b-be45-bf864c304671
-- title:
--   Spreading out a polarised abelian variety with an automorphism
-- statement:
--   Let $k$ be a field, let $u$ be a `PolarisedAbelianScheme g d n k`, so in particular a scheme $u.A$ with a structure morphism $u.f : u.A \to \operatorname{Spec} k$, a relative group law $u.L$, the property bundle (smooth, proper, connected fibres, a group law exists), an invertible module $u.pol$ admitting a `ClosedImmersionBySections` presentation over $u.f$, together with dimension, level and degree data. Let $\sigma$ be a $k$-morphism $u.A \to u.A$ (i.e. $\sigma.1 \circ u.f = u.f$ as sections over $u.f$) with $\sigma.1$ an isomorphism, such that composing with $\sigma$ is a homomorphism for $u.L$ on $T$-points for every $T \to \operatorname{Spec} k$, and such that every point of $\operatorname{Spec} k$ has an open neighbourhood $U$ over which the restrictions of $\sigma.1^{*}u.pol$ and $u.pol$ to $u.f^{-1}U$ are isomorphic. Then there are a finitely generated $\mathbb{Z}$-subalgebra $R \subseteq k$, a scheme $A_0$ with $f_0 : A_0 \to \operatorname{Spec} R$, a relative group law $L_0$, an `AbelianSchemePropertyBundle` for $f_0$ (smoothness, properness, connected fibres, existence of a group law), an invertible $M_0$ on $A_0$ with a closed-immersion-by-sections presentation over $f_0$ (finitely many global sections framing $M_0$ and inducing a closed immersion into projective space over $\operatorname{Spec} R$), an $R$-endomorphism $\sigma_0$ of $A_0$ with $\sigma_0.1$ an isomorphism, which is a homomorphism on points for $L_0$ and satisfies $\sigma_0.1^{*}M_0 \cong M_0$ locally on $\operatorname{Spec} R$, and a morphism $g_A : u.A \to A_0$ making the square with $u.f$, $f_0$ and $\operatorname{Spec}$ of the inclusion $R \hookrightarrow k$ a pullback, such that $g_A$ is compatible with the group laws on $T$-points, $g_A^{*}M_0 \cong u.pol$, and $\sigma.1$ followed by $g_A$ equals $g_A$ followed by $\sigma_0.1$. The level structure, the fibre dimension $g$ and the degree $d$ of $u$ are not transported to the model over $R$; the conclusion asserts only the data listed.
--
--   This is the spreading-out (limit) step for a polarised abelian variety equipped with a polarisation-preserving automorphism: the abelian scheme, the very ample invertible module in its section-presented form, the automorphism and the isomorphism $\sigma^{*}L \cong L$ all descend to a finitely generated $\mathbb{Z}$-subalgebra of $k$, with the original data recovered by base change. It is used to bound the order of such an automorphism over an algebraically closed field by reduction to models over finitely generated rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_closedImmersionBySections_comp_eq_comp_of_isIso_of_pullback_pol_iso.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.PolarisedAbelianScheme

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_fg_subalgebra_abelianScheme_closedImmersionBySections_comp_eq_comp_of_isIso_of_pullback_pol_iso
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
      (M₀ : A₀.Modules) (_ : Scheme.Modules.IsInvertible M₀) (_ : Scheme.Modules.ClosedImmersionBySections M₀ f₀)
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
