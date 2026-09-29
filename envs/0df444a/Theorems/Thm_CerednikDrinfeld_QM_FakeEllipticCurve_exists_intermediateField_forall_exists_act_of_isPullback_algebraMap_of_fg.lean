-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_forall_exists_act_of_isPullback_algebraMap_of_fg
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_intermediateField_forall_exists_act_of_isPullback_algebraMap_of_fg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/b1578a07-654e-5948-809c-b5a055120389
-- title:
--   Descent of a finitely generated quaternionic action to large finite levels
-- statement:
--   Fix rationals $a,b$ and a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ which is finitely generated, and a natural number $N$. Let $K$ be an algebraic extension of a field $k$ and let $L\subseteq K$ be an intermediate field finite over $k$. Let $E$ be a fake elliptic curve with $\Lambda$-action and level-$N$ data over $K$, so in particular a scheme $E.A$ with structure morphism $E.f$ to $\operatorname{Spec} K$, a commutative relative group law $E.L$ on $E.f$, and endomorphisms $E.\mathrm{act}(x)$ of $E.A$ over $K$ for $x\in\Lambda$; only these data enter the statement. Let $f_0:X_0\to\operatorname{Spec} L$ be quasi-compact, quasi-separated and locally of finite type, and let $g:E.A\to X_0$ make the square with $E.f$, $f_0$ and $\operatorname{Spec}$ of $L\to K$ cartesian. Then there is an intermediate field $L_\iota$ with $L\le L_\iota$, finite over $k$, such that the following holds for every intermediate field $L''\ge L_\iota$, every ring homomorphism $j:L\to L''$ compatible with the inclusions into $K$, every $f_2:X_2\to\operatorname{Spec} L''$ together with $r:E.A\to X_2$ cartesian over $\operatorname{Spec}$ of $L''\to K$ and $q:X_2\to X_0$ cartesian over $\operatorname{Spec} j$ with $r$ followed by $q$ equal to $g$, and every relative group law $L_2$ on $f_2$ whose base change along $r$ is $E.L$ (that is, for all $t':T\to\operatorname{Spec} K$ and all $P,Q$ over $t'$, the underlying morphism of $E.L.\mathrm{mul}\,t'\,P\,Q$ followed by $r$ agrees with that of $L_2.\mathrm{mul}$ applied to $P$ and $Q$ composed with $r$): there exist endomorphisms $\mathrm{act}_2(x)$ of $X_2$ for $x\in\Lambda$, each over $L''$ (i.e. $\mathrm{act}_2(x)$ followed by $f_2$ is $f_2$), such that $E.\mathrm{act}(x)$ followed by $r$ equals $r$ followed by $\mathrm{act}_2(x)$; each $\mathrm{act}_2(x)$ is a homomorphism for $L_2$ on points over any base; $\mathrm{act}_2(\langle 1\rangle)=\mathbf{1}_{X_2}$ whenever $1\in\Lambda$; $\mathrm{act}_2(xy)=\mathrm{act}_2(y)$ followed by $\mathrm{act}_2(x)$ whenever $xy\in\Lambda$; and pushing a point forward by $\mathrm{act}_2(x+y)$ equals the $L_2$-product of its pushforwards by $\mathrm{act}_2(x)$ and $\mathrm{act}_2(y)$.
--
--   This is the spreading-out step for the quaternionic action in the construction of models of fake elliptic curves over finite subextensions: the $\Lambda$-action on $E.A/K$, together with the identities `act_over`, `act_hom`, `act_one`, `act_mul` and `act_add` required of a fake elliptic curve, is shown to descend to every model refining a fixed finite level. It is used in assembling a fake elliptic curve over a finite extension of $k$ whose base change to $K$ is $E$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_forall_exists_act_of_isPullback_algebraMap_of_fg.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_intermediateField_forall_exists_act_of_isPullback_algebraMap_of_fg
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : Λ.FG) {N : ℕ}
    (k K : Type) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (L : IntermediateField k K) [FiniteDimensional k ↥L]
    (E : FakeEllipticCurve Λ N K)
    {X₀ : Scheme.{0}} (f₀ : X₀ ⟶ Spec (CommRingCat.of ↥L)) [QuasiCompact f₀] [QuasiSeparated f₀] [LocallyOfFiniteType f₀]
    (g : E.A ⟶ X₀) (hg : CategoryTheory.IsPullback g E.f f₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥L K)))) :
    ∃ (Lι : IntermediateField k K) (_ : FiniteDimensional k ↥Lι) (_ : L ≤ Lι),
      ∀ (L'' : IntermediateField k K) (_ : Lι ≤ L'')
        (j : ↥L →+* ↥L'') (_ : ∀ x : ↥L, ((j x : ↥L'') : K) = (x : K))
        (X₂ : Scheme.{0}) (f₂ : X₂ ⟶ Spec (CommRingCat.of ↥L''))
        (r : E.A ⟶ X₂) (hr : CategoryTheory.IsPullback r E.f f₂ (Spec.map (CommRingCat.ofHom (algebraMap ↥L'' K))))
        (q : X₂ ⟶ X₀) (_ : CategoryTheory.IsPullback q f₂ f₀ (Spec.map (CommRingCat.ofHom j))) (_ : r ≫ q = g)
        (L₂ : RelativeGroupLaw ↥L'' f₂)
        (_ : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t' E.f),
          (E.L.mul t' P Q).1 ≫ r =
            (L₂.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥L'' K)))
              ⟨P.1 ≫ r, by rw [Category.assoc, hr.w, ← Category.assoc, P.2]⟩
              ⟨Q.1 ≫ r, by rw [Category.assoc, hr.w, ← Category.assoc, Q.2]⟩).1),
        ∃ (act₂ : ↥Λ → (X₂ ⟶ X₂)) (hact₂ : ∀ x : ↥Λ, act₂ x ≫ f₂ = f₂),
          (∀ x : ↥Λ, E.act x ≫ r = r ≫ act₂ x) ∧
          (∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥L'')) (P Q : SchemeHomOver t f₂),
            pushPt (act₂ x) (hact₂ x) (L₂.mul t P Q) =
              L₂.mul t (pushPt (act₂ x) (hact₂ x) P) (pushPt (act₂ x) (hact₂ x) Q)) ∧
          (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act₂ ⟨1, h⟩ = 𝟙 X₂) ∧
          (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
            act₂ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act₂ y ≫ act₂ x) ∧
          (∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥L'')) (P : SchemeHomOver t f₂),
            pushPt (act₂ (x + y)) (hact₂ (x + y)) P =
              L₂.mul t (pushPt (act₂ x) (hact₂ x) P) (pushPt (act₂ y) (hact₂ y) P)) := by sorry
