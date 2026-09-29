-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_fstHom_iso_of_bareDeformation_of_act
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_fstHom_iso_of_bareDeformation_of_act
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/34076544-3486-5c06-8ade-10d83ab47408
-- title:
--   First-order bare deformations with Λ-action are fake elliptic curves
-- statement:
--   Fix rationals $a,b$ and a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, let $k$ be an algebraically closed field of characteristic a prime $\ell$, and let $u$ be a fake elliptic curve with $\Lambda$-action of level $1$ over $k$. Regard $k$ as an algebra over the dual numbers $k[\varepsilon]$ via the projection $\varepsilon \mapsto 0$ (`TrivSqZeroExt.fstHom`). Let $D$ be a bare deformation of $(u.f, u.L)$ to $k[\varepsilon]$, i.e. a scheme $D.A$ with a structure morphism $D.f$ to $\operatorname{Spec} k[\varepsilon]$, a commutative relative group law $D.L$, an abelian-scheme property bundle, and a comparison morphism $D.g : u.A \to D.A$ forming a cartesian square over $\varepsilon \mapsto 0$ and compatible with the two group laws on $T$-points; assume $D.f$ is smooth of relative dimension $2$. Let $\mathrm{act} : \Lambda \to \operatorname{End}(D.A)$ satisfy: each $\mathrm{act}\,x$ lies over $D.f$; $\mathrm{act}\,x$ is a homomorphism for $D.L$ on $T$-points; $\mathrm{act}\,1 = \mathrm{id}$ when $1 \in \Lambda$; $\mathrm{act}(xy) = \mathrm{act}\,y$ followed by $\mathrm{act}\,x$ whenever $xy \in \Lambda$; $\mathrm{act}(x+y)$ on points is the $D.L$-product of $\mathrm{act}\,x$ and $\mathrm{act}\,y$; and $u.\mathrm{act}\,x$ followed by $D.g$ equals $D.g$ followed by $\mathrm{act}\,x$. Then there exist a fake elliptic curve $t$ of level $1$ over $k[\varepsilon]$ and a morphism $g_t : u.A \to t.A$ which exhibits $u$ as the pullback of $t$ along $\varepsilon\mapsto 0$ in the sense of `FakeEllipticCurve.IsPullbackVia` (cartesian square, compatibility with the group laws on $T$-points, $\Lambda$-equivariance, and lifting of points factoring through $u.\mathrm{lev}$ to $t.C$), together with an isomorphism $e : t.A \cong D.A$ with $e$ followed by $D.f$ equal to $t.f$, $g_t$ followed by $e$ equal to $D.g$, and $t.\mathrm{act}\,x$ followed by $e$ equal to $e$ followed by $\mathrm{act}\,x$ for all $x \in \Lambda$.
--
--   This is the rigidity step in the deformation theory of fake elliptic curves: a first-order abelian-scheme deformation over $k[\varepsilon]$ carrying a lift of the quaternionic action automatically satisfies the remaining axioms of a fake elliptic curve of level $1$ (fibres of dimension $2$, the trace condition, and a level-$1$ section), so the deformation functor of the moduli problem is computed by bare deformations. It feeds the analysis of unique $k[\varepsilon]$-point liftings for level-one fake elliptic curves over algebraically closed fields of characteristic $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_fstHom_iso_of_bareDeformation_of_act.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_fstHom_iso_of_bareDeformation_of_act
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (k : Type) [Field k] [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (u : FakeEllipticCurve Λ 1 k) :
    letI : Algebra (DualNumber k) k := (TrivSqZeroExt.fstHom k k k).toRingHom.toAlgebra
    ∀ (D : BareDeformation u.f u.L (DualNumber k)) (_ : SmoothOfRelativeDimension 2 D.f)
      (act : ↥Λ → (D.A ⟶ D.A)) (act_over : ∀ x : ↥Λ, act x ≫ D.f = D.f),
      (∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (DualNumber k))) (P Q : SchemeHomOver t D.f),
          pushPt (act x) (act_over x) (D.L.mul t P Q) =
            D.L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q)) →
      (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 D.A) →
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
          act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x) →
      (∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (DualNumber k))) (P : SchemeHomOver t D.f),
          pushPt (act (x + y)) (act_over (x + y)) P =
            D.L.mul t (pushPt (act x) (act_over x) P) (pushPt (act y) (act_over y) P)) →
      (∀ x : ↥Λ, u.act x ≫ D.g = D.g ≫ act x) →
      ∃ (t : FakeEllipticCurve Λ 1 (DualNumber k)) (gt : u.A ⟶ t.A),
        FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.fstHom k k k).toRingHom t u gt ∧
        ∃ e : t.A ≅ D.A, e.hom ≫ D.f = t.f ∧ gt ≫ e.hom = D.g ∧ ∀ x : ↥Λ, t.act x ≫ e.hom = e.hom ≫ act x := by sorry
