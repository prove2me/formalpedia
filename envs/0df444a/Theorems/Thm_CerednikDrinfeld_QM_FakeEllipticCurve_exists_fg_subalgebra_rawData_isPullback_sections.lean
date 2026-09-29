-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_rawData_isPullback_sections
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_rawData_isPullback_sections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/e4d747c3-c2c1-5887-bf0b-27b007dde723
-- title:
--   Descent of fake elliptic curve data and sections to a finitely generated base
-- statement:
--   Let $a,b\in\mathbb{Q}$, let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is a maximal order (an order, maximal among orders for inclusion), let $N\in\mathbb{N}$, let $L$ be a commutative ring, let $E$ be a fake elliptic curve over $L$ with $\Lambda$-action and level-$N$ structure, let $s\subseteq L$ be finite, and let $P_1,\dots,P_n$ be sections of $E.f$, i.e. morphisms $\mathrm{Spec}\,L\to E.A$ composing with $E.f$ to the identity. Then there exist a finitely generated $\mathbb{Z}$-subalgebra $R\subseteq L$ containing $s$ and, over $R$: a scheme $A_0$ with $f_0:A_0\to\mathrm{Spec}\,R$, a relative group law $L_0$ on the functor of points of $f_0$ which is commutative, the property bundle asserting $f_0$ smooth, proper, with connected fibres and admitting a relative group law; maps $\mathrm{act}_0(x):A_0\to A_0$ for $x\in\Lambda$ over $f_0$, additive and multiplicative on $T$-points, with $\mathrm{act}_0(1)=\mathrm{id}$ and $\mathrm{act}_0(xy)=\mathrm{act}_0(x)\circ\mathrm{act}_0(y)$; a closed immersion $\mathrm{lev}_0:C_0\to A_0$ whose factoring points contain the unit, are closed under $L_0$-multiplication and inversion, are killed by $N$ and are $\Lambda$-stable, with $\mathrm{lev}_0$ followed by $f_0$ finite, flat and locally of finite presentation; sections $P'_1,\dots,P'_n$ of $f_0$; and morphisms $g:E.A\to A_0$, $g_C:E.C\to C_0$ making $E.f$ cartesian over $f_0$ along $\mathrm{Spec}(R\hookrightarrow L)$ and $E.\mathrm{lev}$ cartesian over $\mathrm{lev}_0$ along $g$, such that $g$ is a homomorphism on $T$-points, is $\Lambda$-equivariant ($E.\mathrm{act}(x)$ followed by $g$ equals $g$ followed by $\mathrm{act}_0(x)$), and $P_k$ followed by $g$ equals $\mathrm{Spec}(R\hookrightarrow L)$ followed by $P'_k$. The data produced over $R$ is the raw data with its laws; the fibre-dimension and trace conditions belonging to `FakeEllipticCurve` are not asserted.
--
--   This is the limit (spreading-out) step for fake elliptic curves: all of the structure of $E$, together with finitely many prescribed sections and finitely many prescribed elements of $L$, already lives over a finitely generated $\mathbb{Z}$-subalgebra of $L$, and $E$ is recovered by base change. It refines the version without sections and is used in turn by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_isPullback_levelIff_sections`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_isPullback_levelIff_sections) in the analysis of the moduli problem over general base rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_rawData_isPullback_sections.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_rawData_isPullback_sections
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N : ℕ)
    (L : Type) [CommRing L] (E : FakeEllipticCurve Λ N L) (s : Finset L)
    {n : ℕ} (P : Fin n → SchemeHomOver (𝟙 (Spec (CommRingCat.of L))) E.f) :
    ∃ (R : Subalgebra ℤ L) (_ : R.FG) (_ : (↑s : Set L) ⊆ R)
      (A₀ : Scheme.{0}) (f₀ : A₀ ⟶ Spec (CommRingCat.of ↥R)) (L₀ : RelativeGroupLaw ↥R f₀) (_ : L₀.IsCommutative)
      (_ : AbelianSchemePropertyBundle ↥R f₀)
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
      (P' : Fin n → SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥R))) f₀)
      (g : E.A ⟶ A₀) (hg : CategoryTheory.IsPullback g E.f f₀ (Spec.map (CommRingCat.ofHom R.val.toRingHom)))
      (gC : E.C ⟶ C₀) (_ : CategoryTheory.IsPullback gC E.lev lev₀ g),
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of L)) (P Q : SchemeHomOver t' E.f),
        (E.L.mul t' P Q).1 ≫ g =
          (L₀.mul (t' ≫ Spec.map (CommRingCat.ofHom R.val.toRingHom))
            ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, E.act x ≫ g = g ≫ act₀ x) ∧
      (∀ k, (P k).1 ≫ g = Spec.map (CommRingCat.ofHom R.val.toRingHom) ≫ (P' k).1) := by sorry
