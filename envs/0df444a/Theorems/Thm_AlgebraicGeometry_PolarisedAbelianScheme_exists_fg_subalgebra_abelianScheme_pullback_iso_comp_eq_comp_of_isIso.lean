-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_pullback_iso_comp_eq_comp_of_isIso
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.exists_fg_subalgebra_abelianScheme_pullback_iso_comp_eq_comp_of_isIso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/3162832d-7662-5ca3-8de8-26cdccd3f807
-- title:
--   Spreading out an abelian variety with automorphism and invertible module
-- statement:
--   Fix natural numbers $g,d,n$ and a field $k$ (in the bottom universe), and let $u$ be a `PolarisedAbelianScheme g d n k`: a scheme $u.A$ with a morphism $u.f : u.A \to \operatorname{Spec} k$, a relative group law $u.L$ on $u.f$ that is commutative, the bundle of properties recording that $u.f$ is smooth, proper, has connected fibres and admits a relative group law, fibres of topological Krull dimension $g$, a family $u.P$ of $2g$ sections killed by $n$ which freely generate the $n$-torsion of every geometric fibre, and an invertible module $u.\mathrm{pol}$ on $u.A$ which defines a closed immersion by sections over $u.f$ and has $H^0$ of rank $d$ on all geometric fibres. Let $\sigma$ be a morphism $u.A \to u.A$ over $\operatorname{Spec} k$ whose underlying scheme morphism is an isomorphism and which is multiplicative on points: for every $t : T \to \operatorname{Spec} k$ and all $x,y$ in $\operatorname{Hom}_t(T,u.A)$, post-composition with $\sigma$ takes $u.L.\mathrm{mul}\,t\,x\,y$ to $u.L.\mathrm{mul}\,t\,(x\sigma)\,(y\sigma)$. The conclusion asserts the existence of a finitely generated $\mathbb Z$-subalgebra $R \subseteq k$, a scheme $A_0$ with a morphism $f_0 : A_0 \to \operatorname{Spec} R$, a relative group law $L_0$ on $f_0$, the property bundle for $f_0$ (smooth, proper, connected fibres, a relative group law exists), the predicate `GeometricallyConnected f₀`, an invertible module $M_0$ on $A_0$, a morphism $\sigma_0 : A_0 \to A_0$ over $\operatorname{Spec} R$ whose underlying morphism is an isomorphism and which is multiplicative on $T$-points for $L_0$ in the same sense, and a morphism $g_A : u.A \to A_0$ making the square with $u.f$, $f_0$ and $\operatorname{Spec}$ of the inclusion $R \hookrightarrow k$ cartesian, such that: $g_A$ is compatible with the group laws on points, i.e. $(u.L.\mathrm{mul}\,t\,x\,y)$ followed by $g_A$ equals $L_0.\mathrm{mul}$ of the images of $x$ and $y$ over the base-changed $t$; the pullback of $M_0$ along $g_A$ is isomorphic to $u.\mathrm{pol}$; and $\sigma$ followed by $g_A$ equals $g_A$ followed by $\sigma_0$. Note that the descended data are not required to carry the full polarised structure: nothing is asserted about sections descending the points $u.P$, about $M_0$ defining a closed immersion by sections over $f_0$, about the geometric fibre ranks, about commutativity of $L_0$, or about $\sigma_0$ preserving $M_0$.
--
--   This is a spreading-out statement in the style of the limit arguments of EGA IV §8: an abelian variety over a field, together with an automorphism that is a group homomorphism and an invertible module, descends to a finitely generated $\mathbb Z$-subalgebra of the base field, the original data being recovered by base change. It is an intermediate stage towards the version that in addition transports the polarisation data, and is used by [`AlgebraicGeometry.PolarisedAbelianScheme.exists_fg_subalgebra_abelianScheme_pullback_iso_comp_eq_comp_of_isIso_of_pullback_pol_iso`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.exists_fg_subalgebra_abelianScheme_pullback_iso_comp_eq_comp_of_isIso_of_pullback_pol_iso).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_pullback_iso_comp_eq_comp_of_isIso.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.PolarisedAbelianScheme

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_fg_subalgebra_abelianScheme_pullback_iso_comp_eq_comp_of_isIso
    {g d n : ℕ} {k : Type} [Field k] (u : PolarisedAbelianScheme g d n k)
    (σ : SchemeHomOver u.f u.f) (hσiso : IsIso σ.1)
    (hσ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t u.f),
      NeronModelInfra.schemeHomOverComp (u.L.mul t x y) σ =
        u.L.mul t (NeronModelInfra.schemeHomOverComp x σ) (NeronModelInfra.schemeHomOverComp y σ)) :
    ∃ (R : Subalgebra ℤ k) (_ : R.FG)
      (A₀ : Scheme.{0}) (f₀ : A₀ ⟶ Spec (CommRingCat.of ↥R)) (L₀ : RelativeGroupLaw ↥R f₀)
      (_ : AbelianSchemePropertyBundle ↥R f₀)
      (_ : GeometricallyConnected f₀)
      (M₀ : A₀.Modules) (_ : Scheme.Modules.IsInvertible M₀)
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
      Nonempty ((Scheme.Modules.pullback gA).obj M₀ ≅ u.pol) ∧
      σ.1 ≫ gA = gA ≫ σ₀.1 := by sorry
