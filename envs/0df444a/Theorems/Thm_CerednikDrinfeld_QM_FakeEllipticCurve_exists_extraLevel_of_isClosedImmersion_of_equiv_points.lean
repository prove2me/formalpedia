-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_of_isClosedImmersion_of_equiv_points
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_of_isClosedImmersion_of_equiv_points
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/4912484e-4879-5057-b569-238f6900449e
-- title:
--   Extra ℓ-level recognised from its k-points
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, a prime $\ell$, and an algebraically closed field $k$ in which $\ell \neq 0$; let $E$ be a fake elliptic curve of type $(\Lambda,N)$ over $k$, with structure morphism $E.f : E.A \to \operatorname{Spec} k$, commutative relative group law $E.L$, action $E.\mathrm{act}$ of $\Lambda$ by morphisms over $E.f$, and level structure $E.\mathrm{lev}$. Let $g : B \to \operatorname{Spec} k$ be a scheme over $k$ carrying a relative group law $LB$, and let $i$ be a morphism $B \to E.A$ with $i \circ$ (i.e. followed by) $E.f$ equal to $g$. Assume: $B$ is reduced, $g$ is finite and étale, the underlying morphism of $i$ is a closed immersion, and $i$ is a homomorphism, in the sense that for every $t : T \to \operatorname{Spec} k$ and all $T$-points $x,y$ of $B$ over $t$ one has $(LB.\mathrm{mul}\,t\,x\,y)$ followed by $i$ equal to $E.L.\mathrm{mul}\,t$ of $x$ followed by $i$ and $y$ followed by $i$. Let $S$ be a set of $k$-points of $E.A$ (sections of $E.f$ over the identity of $\operatorname{Spec} k$), together with a bijection $eB$ from the $k$-points of $g$ onto $S$ given by composition with $i$, and a bijection $e : \mathbb{Z}/\ell \times \mathbb{Z}/\ell \to S$ carrying addition to $E.L.\mathrm{mul}$. Assume further that $S$ is stable under the pushforward of points by $E.\mathrm{act}\,m$ for every $m \in \Lambda$, and that any $P \in S$ which factors through $E.\mathrm{lev}$ is the identity section. Then there exists an extra $\ell$-level $K$ on $E$ — a closed immersion $K.\mathrm{lev}K$ into $E.A$ whose factoring points form a subgroup for $E.L$, are killed by $\ell$, are stable under $\Lambda$ and meet $E.\mathrm{lev}$ only in the identity, with $K.\mathrm{lev}K$ followed by $E.f$ finite, flat and locally of finite presentation of rank $\ell^2$ and with geometric fibres $\mathbb{Z}/\ell \times \mathbb{Z}/\ell$ — such that for every $t : T \to \operatorname{Spec} k$ a point $P$ of $E.A$ over $t$ factors through $K.\mathrm{lev}K$ if and only if it factors through $i$, and a $k$-point $P$ factors through $K.\mathrm{lev}K$ if and only if $P \in S$.
--
--   This is the recognition criterion for an auxiliary $\ell$-level structure on a fake elliptic curve over an algebraically closed field: a reduced finite étale closed subgroup scheme whose $k$-points form a $\Lambda$-stable copy of $(\mathbb{Z}/\ell)^2$ meeting the given level structure trivially is already an extra $\ell$-level, and its functor of points agrees with that of the subgroup scheme on all test schemes. It is used in the construction of fake elliptic curves with extra $\ell$-level and in the comparison of such data under level isogenies.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_of_isClosedImmersion_of_equiv_points.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_of_isClosedImmersion_of_equiv_points
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) {N : ℕ}
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type) [Field k] [IsAlgClosed k] (hℓk : (ℓ : k) ≠ 0)
    (E : FakeEllipticCurve Λ N k)
    (B : Scheme.{0}) (g : B ⟶ Spec (CommRingCat.of k)) (LB : RelativeGroupLaw k g) (i : SchemeHomOver g E.f)
    (hred : IsReduced B) (hfin : IsFinite g) (hget : Etale g) (hci : IsClosedImmersion i.1)
    (hhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t g),
      NeronModelInfra.schemeHomOverComp (LB.mul t x y) i =
        E.L.mul t (NeronModelInfra.schemeHomOverComp x i) (NeronModelInfra.schemeHomOverComp y i))
    (S : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f))
    (eB : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g ≃ ↥S)
    (heB : ∀ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g,
      ((eB y : ↥S) : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f) = NeronModelInfra.schemeHomOverComp y i)
    (e : ZMod ℓ × ZMod ℓ ≃ ↥S)
    (he : ∀ x y : ZMod ℓ × ZMod ℓ,
      ((e (x + y) : ↥S) : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f) =
        E.L.mul (𝟙 (Spec (CommRingCat.of k))) (e x) (e y))
    (hstab : ∀ (m : ↥Λ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f),
      P ∈ S → pushPt (E.act m) (E.act_over m) P ∈ S)
    (hdisj : ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f,
      P ∈ S → FactorsThrough E.lev P → P = E.L.one (𝟙 (Spec (CommRingCat.of k)))) :
    ∃ K : E.ExtraLevel ℓ,
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f),
        FactorsThrough K.levK P ↔ FactorsThrough i.1 P) ∧
      (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f, FactorsThrough K.levK P ↔ P ∈ S) := by sorry
