-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_level_isPullback
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_abelianScheme_act_level_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/7b1853be-bcf3-532c-ba47-9e65cfade9bb
-- title:
--   Descent of fake elliptic curve data to a finitely generated subalgebra
-- statement:
--   Let $a,b\in\mathbb{Q}$, let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is an order maximal among orders, let $N\in\mathbb{N}$, let $L$ be a commutative ring, let $E$ be a fake elliptic curve over $L$ for $\Lambda$ and $N$, and let $s\subseteq L$ be finite. Then there are a finitely generated $\mathbb{Z}$-subalgebra $R\subseteq L$ containing $s$ and, over $R$: a scheme $A_0$ with a morphism $f_0\colon A_0\to\operatorname{Spec}R$, a relative group law $L_0$ on $f_0$ (a group structure, natural in base change, on the sections of $f_0$ over each $t\colon T\to\operatorname{Spec}R$) that is commutative, with $f_0$ smooth, proper, with connected fibres, admitting a relative group law, and geometrically connected; a map $\mathrm{act}_0\colon\Lambda\to\operatorname{End}(A_0)$ with $\mathrm{act}_0(x)$ over $\operatorname{Spec}R$, acting on points by group homomorphisms, sending $1$ to $\mathbb{1}_{A_0}$, satisfying $\mathrm{act}_0(xy)=\mathrm{act}_0(y)$ followed by $\mathrm{act}_0(x)$, and additive in $x$ on points; a closed immersion $\mathrm{lev}_0\colon C_0\to A_0$ whose points (sections factoring through $\mathrm{lev}_0$) are closed under the law and inversion, contain the unit, are annihilated by $N$ and are $\mathrm{act}_0$-stable, with $\mathrm{lev}_0$ followed by $f_0$ finite, flat and locally of finite presentation; and comparison morphisms $g\colon E.A\to A_0$ making $E.f$, $f_0$ and $\operatorname{Spec}$ of $R\hookrightarrow L$ a pullback square, and $g_C\colon E.C\to C_0$ making $E.\mathrm{lev}$, $\mathrm{lev}_0$ and $g$ a pullback square, such that $g$ carries products for $E.L$ to products for $L_0$ over the base change, and $E.\mathrm{act}(x)$ followed by $g$ equals $g$ followed by $\mathrm{act}_0(x)$ for all $x\in\Lambda$. The descended data are not asserted to satisfy the remaining axioms of a fake elliptic curve over $R$ (fibre dimension and the trace condition on the $\Lambda$-action are absent).
--
--   This is a spreading-out (limit) step for the moduli problem of fake elliptic curves: the abelian scheme underlying a fake elliptic curve over an arbitrary commutative ring, together with its quaternionic action and its level-$N$ subscheme and the laws these satisfy, already lives over a finitely generated $\mathbb{Z}$-subalgebra, the original data being recovered by base change. It feeds [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_rawData_isPullback_sections`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_rawData_isPullback_sections), where finitely many sections are descended as well.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_level_isPullback.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_abelianScheme_act_level_isPullback
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N : ℕ)
    (L : Type) [CommRing L] (E : FakeEllipticCurve Λ N L) (s : Finset L) :
    ∃ (R : Subalgebra ℤ L) (_ : R.FG) (_ : (↑s : Set L) ⊆ R)
      (A₀ : Scheme.{0}) (f₀ : A₀ ⟶ Spec (CommRingCat.of ↥R)) (L₀ : RelativeGroupLaw ↥R f₀) (_ : L₀.IsCommutative)
      (_ : AbelianSchemePropertyBundle ↥R f₀)
      (_ : GeometricallyConnected f₀)
      (act₀ : ↥Λ → (A₀ ⟶ A₀)) (hact_over₀ : ∀ x : ↥Λ, act₀ x ≫ f₀ = f₀)
      (_ : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥R)) (P Q : SchemeHomOver t f₀),
        pushPt (act₀ x) (hact_over₀ x) (L₀.mul t P Q) = L₀.mul t (pushPt (act₀ x) (hact_over₀ x) P) (pushPt (act₀ x) (hact_over₀ x) Q))
      (_ : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act₀ ⟨1, h⟩ = 𝟙 A₀)
      (_ : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
        act₀ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act₀ y ≫ act₀ x)
      (_ : ∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥R)) (P : SchemeHomOver t f₀),
        pushPt (act₀ (x + y)) (hact_over₀ (x + y)) P =
          L₀.mul t (pushPt (act₀ x) (hact_over₀ x) P) (pushPt (act₀ y) (hact_over₀ y) P))
      (C₀ : Scheme.{0}) (lev₀ : C₀ ⟶ A₀) (_ : IsClosedImmersion lev₀)
      (_ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥R)) (P Q : SchemeHomOver t f₀),
        FactorsThrough lev₀ P → FactorsThrough lev₀ Q → FactorsThrough lev₀ (L₀.mul t P Q) ∧ FactorsThrough lev₀ (L₀.inv t P))
      (_ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥R)), FactorsThrough lev₀ (L₀.one t))
      (_ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥R)) (P : SchemeHomOver t f₀),
        FactorsThrough lev₀ P → nsmulPt L₀ t N P = L₀.one t)
      (_ : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥R)) (P : SchemeHomOver t f₀),
        FactorsThrough lev₀ P → FactorsThrough lev₀ (pushPt (act₀ x) (hact_over₀ x) P))
      (_ : IsFinite (lev₀ ≫ f₀)) (_ : Flat (lev₀ ≫ f₀)) (_ : LocallyOfFinitePresentation (lev₀ ≫ f₀))
      (g : E.A ⟶ A₀) (hg : CategoryTheory.IsPullback g E.f f₀ (Spec.map (CommRingCat.ofHom R.val.toRingHom)))
      (gC : E.C ⟶ C₀) (_ : CategoryTheory.IsPullback gC E.lev lev₀ g),
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of L)) (P Q : SchemeHomOver t' E.f),
        (E.L.mul t' P Q).1 ≫ g =
          (L₀.mul (t' ≫ Spec.map (CommRingCat.ofHom R.val.toRingHom))
            ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, E.act x ≫ g = g ≫ act₀ x) := by sorry
