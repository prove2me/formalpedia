-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/80b00f26-f5ad-5f2b-baea-8d199f45db52
-- title:
--   Spreading out a polarised abelian variety: the Proj presentation stage
-- statement:
--   Let $g,d,n$ be natural numbers, $k$ a field, and $u$ a polarised abelian scheme over $k$ of the project's kind: a scheme $A$ with structure morphism $f : A \to \operatorname{Spec} k$, a commutative relative group law $L$, the property bundle (smooth, proper, connected fibres, group law present), fibres of topological Krull dimension $g$, $2g$ sections generating the $n$-torsion freely over every algebraically closed field, and an invertible module $\mathcal L = u.\mathrm{pol}$ admitting a closed immersion by global sections with geometric fibre $H^0$-rank $d$. Let $\sigma : A \to A$ be a morphism over $\operatorname{Spec} k$ whose underlying morphism is an isomorphism, compatible with $L$ in the sense that composing a product of two $T$-points with $\sigma$ gives the product of their composites with $\sigma$, and assume that each point of $\operatorname{Spec} k$ has an open neighbourhood $U$ over which $\sigma^{*}\mathcal L$ and $\mathcal L$ become isomorphic after restriction to $f^{-1}U$. Then there exist a finitely generated $\mathbb Z$-subalgebra $R \subseteq k$, a scheme $A_0$ with $f_0 : A_0 \to \operatorname{Spec} R$, a relative group law $L_0$, the abelian-scheme property bundle for $f_0$, the predicate `GeometricallyConnected` for $f_0$, an invertible $A_0$-module $M_0$, a morphism $\sigma_0 : A_0 \to A_0$ over $\operatorname{Spec} R$ with underlying isomorphism, compatible with $L_0$ on points and with $\sigma_0^{*}M_0 \cong M_0$ locally on $\operatorname{Spec} R$ in the same sense as above, and a morphism $g_A : A \to A_0$ making $A$ the pullback of $f_0$ along $\operatorname{Spec} k \to \operatorname{Spec} R$, compatible with the two group laws on points, with $g_A^{*}M_0 \cong \mathcal L$ and $\sigma$ followed by $g_A$ equal to $g_A$ followed by $\sigma_0$; and moreover there exist a finitely generated $\mathbb Z$-subalgebra $T$ with $R \le T \subseteq k$, an $N \in \mathbb N$ and a `ProjPresentation` $\mathfrak P$ of the pullback of $M_0$ to $A_0 \times_{\operatorname{Spec} R} \operatorname{Spec} T$ over $\operatorname{Spec} T$ by $N+1$ global sections — that is, sections $\tau_0,\dots,\tau_N$ together with $\varphi = \mathfrak P.\mathrm{toProj}$ into $\mathbb P^N_T$ over $\operatorname{Spec} T$ such that $\tau_i$ frames the module over the preimage of the $i$-th standard basic open and the sections transform by the coordinate ratios — with the property that every morphism $m_A$ from the pullback of $\varphi$ followed by $\mathbb P^N_T \to \operatorname{Spec} T$ along $\operatorname{Spec} k \to \operatorname{Spec} T$ to the pullback of $\mathbb P^N_T \to \operatorname{Spec} T$ along the same morphism, which is compatible with the first projections through $\varphi$ and with the second projections, is a closed immersion. The conclusion gives the data over $R$ individually; it does not assemble them into a polarised abelian scheme over $R$, and asserts nothing about torsion sections, fibre dimension or fibre rank over $R$.
--
--   This is the stage of the spreading-out argument for a polarised abelian variety carrying an automorphism at which the very ample module over the finitely generated base acquires a presentation by global sections whose base change to $k$ is a closed immersion. It is used by the next stage, where $T$ is enlarged once more so that the presenting morphism into projective space is itself a closed immersion, yielding a closed immersion by sections over a finitely generated $\mathbb Z$-subalgebra of $k$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.PolarisedAbelianScheme

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso
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
      σ.1 ≫ gA = gA ≫ σ₀.1 ∧
      ∃ (T : Subalgebra ℤ k) (hRT : R ≤ T) (_ : T.FG) (N : ℕ)
        (𝔓 : Scheme.Modules.ProjPresentation
          ((Scheme.Modules.pullback
            (pullback.fst f₀ (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRT).toRingHom)))).obj M₀)
          (pullback.snd f₀ (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRT).toRingHom))) N),
        ∀ mA : pullback (𝔓.toProj ≫ ProjSpace.π ↥T N) (Spec.map (CommRingCat.ofHom (algebraMap ↥T k))) ⟶
            pullback (ProjSpace.π ↥T N) (Spec.map (CommRingCat.ofHom (algebraMap ↥T k))),
          mA ≫ pullback.fst _ _ = pullback.fst _ _ ≫ 𝔓.toProj → mA ≫ pullback.snd _ _ = pullback.snd _ _ →
          IsClosedImmersion mA := by sorry
