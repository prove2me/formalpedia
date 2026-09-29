-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_levelData_isPullback
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_abelianScheme_act_levelData_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/60c5809b-994b-528b-a6b5-39ff66b42765
-- title:
--   Descent of fake elliptic curve data and level subscheme
-- statement:
--   Let $a,b\in\mathbb Q$, let $\Lambda\subseteq\mathbb H[\mathbb Q,a,b]$ be a $\mathbb Z$-submodule which is a maximal order (an order, maximal among orders containing it), let $N\in\mathbb N$, let $L$ be a commutative ring, let $E$ be a fake elliptic curve of level $N$ with $\Lambda$-action over $L$, and let $s\subseteq L$ be finite. Then there is a finitely generated $\mathbb Z$-subalgebra $R\subseteq L$ containing $s$ carrying the following data: a scheme $A_0$ with a morphism $f_0\colon A_0\to\operatorname{Spec}R$; a relative group law $L_0$ on $f_0$, i.e. a functorial group structure on the sets of $T$-points over $\operatorname{Spec}R$, which is commutative; the bundle of properties asserting $f_0$ smooth and proper with connected fibres and admitting a relative group law; the predicate `GeometricallyConnected` for $f_0$; maps $\mathrm{act}_0\colon\Lambda\to\operatorname{End}(A_0)$ over $\operatorname{Spec}R$ that are homomorphisms for $L_0$ on points, send $1$ to $\mathbf 1_{A_0}$, satisfy $\mathrm{act}_0(xy)=\mathrm{act}_0(x)\circ\mathrm{act}_0(y)$ and are additive on points; a closed immersion $\mathrm{lev}_0\colon C_0\to A_0$ with $\mathrm{lev}_0$ followed by $f_0$ finite, flat and locally of finite presentation; and comparison morphisms $g\colon E.A\to A_0$, $g_C\colon E.C\to C_0$ making the squares $(g,E.f,f_0,\operatorname{Spec}R\leftarrow\operatorname{Spec}L)$ and $(g_C,E.\mathrm{lev},\mathrm{lev}_0,g)$ cartesian, with $g$ a homomorphism on $T$-points and $\Lambda$-equivariant: $E.\mathrm{act}(x)$ followed by $g$ equals $g$ followed by $\mathrm{act}_0(x)$. No fibre-dimension or trace condition is asserted for the model, so the descended data is not claimed to be a fake elliptic curve over $R$.
--
--   This is a stage of the descent (spreading out) of the raw data of a fake elliptic curve from an arbitrary base ring to a finitely generated $\mathbb Z$-subalgebra, here adding the level subscheme $C_0\hookrightarrow A_0$ with its finiteness, flatness and finite presentation over the base to the abelian scheme and the $\Lambda$-action obtained earlier. It is used by the further stage [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_abelianScheme_act_level_isPullback`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_abelianScheme_act_level_isPullback) in the construction of the moduli of fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_act_levelData_isPullback.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_abelianScheme_act_levelData_isPullback
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
      (_ : IsFinite (lev₀ ≫ f₀)) (_ : Flat (lev₀ ≫ f₀)) (_ : LocallyOfFinitePresentation (lev₀ ≫ f₀))
      (g : E.A ⟶ A₀) (hg : CategoryTheory.IsPullback g E.f f₀ (Spec.map (CommRingCat.ofHom R.val.toRingHom)))
      (gC : E.C ⟶ C₀) (_ : CategoryTheory.IsPullback gC E.lev lev₀ g),
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of L)) (P Q : SchemeHomOver t' E.f),
        (E.L.mul t' P Q).1 ≫ g =
          (L₀.mul (t' ≫ Spec.map (CommRingCat.ofHom R.val.toRingHom))
            ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, E.act x ≫ g = g ≫ act₀ x) := by sorry
