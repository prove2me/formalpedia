-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_endomorphisms_isPullback
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_abelianScheme_endomorphisms_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/0b6c246d-ad75-5ff6-b22e-d7f8a2f45b32
-- title:
--   Descent of a fake elliptic curve's abelian scheme with endomorphisms
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, a commutative ring $L$, and a fake elliptic curve $E$ of type $(\Lambda,N)$ over $L$; from the data of $E$ only the scheme $E.A$, its structure morphism $E.f\colon E.A\to\operatorname{Spec} L$ and its relative group law $E.L$ enter the conclusion. Let $s$ be a finite subset of $L$ and let $\varphi\colon\iota\to(E.A\to E.A)$ be a finite family of endomorphisms of $E.A$ over $\operatorname{Spec} L$, i.e. $\varphi_i$ followed by $E.f$ equals $E.f$ for each $i$. Then there exist a finitely generated $\mathbb{Z}$-subalgebra $R\subseteq L$ whose underlying set contains $s$, a scheme $A_0$, a morphism $f_0\colon A_0\to\operatorname{Spec} R$, a relative group law $L_0$ for $f_0$ (a group structure, natural in $T$, on the sections of $f_0$ over each $t\colon T\to\operatorname{Spec} R$) which is commutative, such that $f_0$ satisfies `AbelianSchemePropertyBundle` (smooth, proper, with connected fibres, and admitting a relative group law) and is geometrically connected, together with endomorphisms $\varphi_{0,i}$ of $A_0$ over $\operatorname{Spec} R$ and a morphism $g\colon E.A\to A_0$ for which the square formed by $g$, $E.f$, $f_0$ and $\operatorname{Spec}$ of the inclusion $R\hookrightarrow L$ is cartesian, $g$ carries the group law $E.L$ to $L_0$ on sections (for all $T$, all $t'\colon T\to\operatorname{Spec} L$ and all sections $P,Q$ of $E.f$ over $t'$, composing $E.L.\mathrm{mul}\,t'\,P\,Q$ with $g$ gives the $L_0$-product of $P$ followed by $g$ and $Q$ followed by $g$ over $t'$ composed with $\operatorname{Spec}$ of the inclusion), and $\varphi_i$ followed by $g$ equals $g$ followed by $\varphi_{0,i}$ for every $i$.
--
--   This is the first stage of a telescoping descent of the data of a fake elliptic curve from a commutative ring $L$ to a finitely generated $\mathbb{Z}$-subalgebra: it descends the abelian scheme, its relative group law and a finite family of endomorphisms, but not yet the $\Lambda$-action or the level data, so its conclusion is a prefix of the full descent statement; the extra geometric connectedness of $f_0$ is recorded so that later stages may base-change the model. It is used by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_abelianScheme_act_isPullback`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_abelianScheme_act_isPullback), which adds the $\Lambda$-action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_abelianScheme_endomorphisms_isPullback.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_abelianScheme_endomorphisms_isPullback
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N : ℕ)
    (L : Type) [CommRing L] (E : FakeEllipticCurve Λ N L) (s : Finset L)
    {ι : Type} [Finite ι] (φ : ι → (E.A ⟶ E.A)) (hφ : ∀ i, φ i ≫ E.f = E.f) :
    ∃ (R : Subalgebra ℤ L) (_ : R.FG) (_ : (↑s : Set L) ⊆ R)
      (A₀ : Scheme.{0}) (f₀ : A₀ ⟶ Spec (CommRingCat.of ↥R)) (L₀ : RelativeGroupLaw ↥R f₀) (_ : L₀.IsCommutative)
      (_ : AbelianSchemePropertyBundle ↥R f₀)
      (_ : GeometricallyConnected f₀)
      (φ₀ : ι → (A₀ ⟶ A₀)) (_ : ∀ i, φ₀ i ≫ f₀ = f₀)
      (g : E.A ⟶ A₀) (hg : CategoryTheory.IsPullback g E.f f₀ (Spec.map (CommRingCat.ofHom R.val.toRingHom))),
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of L)) (P Q : SchemeHomOver t' E.f),
        (E.L.mul t' P Q).1 ≫ g =
          (L₀.mul (t' ≫ Spec.map (CommRingCat.ofHom R.val.toRingHom))
            ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ i, φ i ≫ g = g ≫ φ₀ i) := by sorry
