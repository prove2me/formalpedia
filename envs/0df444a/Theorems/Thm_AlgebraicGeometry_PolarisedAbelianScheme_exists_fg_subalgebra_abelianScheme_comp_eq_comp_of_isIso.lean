-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_comp_eq_comp_of_isIso
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.exists_fg_subalgebra_abelianScheme_comp_eq_comp_of_isIso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/5bbad299-351c-533a-a724-aa5934e2d6b5
-- title:
--   Spreading out an abelian variety with an automorphism
-- statement:
--   Let $k$ be a field and let $u$ be a polarised abelian scheme datum of type $(g,d,n)$ over $k$: a scheme $A = u.A$ with structure morphism $f = u.f : A \to \operatorname{Spec} k$, a commutative relative group law $u.L$ on the functor of points of $f$, the bundle of properties (smooth, proper, connected fibres, group law available), fibres of topological Krull dimension $g$, $2g$ sections of $n$-torsion that form a basis of the $n$-torsion of every geometric fibre, and an invertible module $u.\mathrm{pol}$ embedding $A$ by sections with geometric fibre $H^0$-rank $d$. Let $\sigma$ be a morphism $A \to A$ over $\operatorname{Spec} k$ whose underlying morphism is an isomorphism and which is a homomorphism for $u.L$, in the sense that postcomposition with $\sigma$ carries $u.L.\mathrm{mul}\,t\,x\,y$ to the product of the postcompositions, for all $T$, all $t : T \to \operatorname{Spec} k$ and all $T$-points $x,y$ over $t$. Then there are a finitely generated $\mathbb{Z}$-subalgebra $R \subseteq k$, a scheme $A_0$ with $f_0 : A_0 \to \operatorname{Spec} R$ carrying a relative group law $L_0$, the property bundle for $f_0$ and geometric connectedness of $f_0$, an automorphism $\sigma_0$ of $A_0$ over $\operatorname{Spec} R$ that is a homomorphism for $L_0$ in the same sense, and a morphism $g_A : A \to A_0$ making the square with $f$, $f_0$ and $\operatorname{Spec}$ of the inclusion $R \hookrightarrow k$ cartesian, such that $g_A$ transports $u.L$-products to $L_0$-products on points and $\sigma$ followed by $g_A$ equals $g_A$ followed by $\sigma_0$. No polarisation, torsion sections or commutativity are asserted for $L_0$ in the conclusion.
--
--   This is the first stage of a spreading-out (Grothendieck limit) argument: an abelian variety over a field, together with an automorphism compatible with the group law, descends to an abelian scheme with automorphism over a finitely generated $\mathbb{Z}$-subalgebra of the field, the original data being recovered by base change. It is used by [`AlgebraicGeometry.PolarisedAbelianScheme.exists_fg_subalgebra_abelianScheme_pullback_iso_comp_eq_comp_of_isIso`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.exists_fg_subalgebra_abelianScheme_pullback_iso_comp_eq_comp_of_isIso), where the polarising module and the remaining structure are carried along as well.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_comp_eq_comp_of_isIso.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.PolarisedAbelianScheme

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_fg_subalgebra_abelianScheme_comp_eq_comp_of_isIso
    {g d n : ℕ} {k : Type} [Field k] (u : PolarisedAbelianScheme g d n k)
    (σ : SchemeHomOver u.f u.f) (hσiso : IsIso σ.1)
    (hσ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t u.f),
      NeronModelInfra.schemeHomOverComp (u.L.mul t x y) σ =
        u.L.mul t (NeronModelInfra.schemeHomOverComp x σ) (NeronModelInfra.schemeHomOverComp y σ)) :
    ∃ (R : Subalgebra ℤ k) (_ : R.FG)
      (A₀ : Scheme.{0}) (f₀ : A₀ ⟶ Spec (CommRingCat.of ↥R)) (L₀ : RelativeGroupLaw ↥R f₀)
      (_ : AbelianSchemePropertyBundle ↥R f₀)
      (_ : GeometricallyConnected f₀)
      (σ₀ : SchemeHomOver f₀ f₀) (_ : IsIso σ₀.1)
      (_ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥R)) (x y : SchemeHomOver t f₀),
        NeronModelInfra.schemeHomOverComp (L₀.mul t x y) σ₀ =
          L₀.mul t (NeronModelInfra.schemeHomOverComp x σ₀) (NeronModelInfra.schemeHomOverComp y σ₀))
      (gA : u.A ⟶ A₀) (hg : CategoryTheory.IsPullback gA u.f f₀ (Spec.map (CommRingCat.ofHom R.val.toRingHom))),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t u.f),
        (u.L.mul t x y).1 ≫ gA =
          (L₀.mul (t ≫ Spec.map (CommRingCat.ofHom R.val.toRingHom))
            ⟨x.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
            ⟨y.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1) ∧
      σ.1 ≫ gA = gA ≫ σ₀.1 := by sorry
