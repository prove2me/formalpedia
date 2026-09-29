-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_algebraMap_of_abelianSchemePropertyBundle_of_isPullback
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_algebraMap_of_abelianSchemePropertyBundle_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/72dbc5ce-0277-53f7-b913-023cda829b14
-- title:
--   Extending a fake elliptic curve from K to a DVR R
-- statement:
--   Fix $a,b\in\mathbb{Q}$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, and a natural number $N$; let $R$ be a discrete valuation domain with fraction field $K$, and assume the image of $N$ in $R$ is a unit. Let $E$ be a fake elliptic curve over $K$ in the sense of `FakeEllipticCurve Λ N K`, i.e. a scheme `E.A` with structure morphism `E.f` to $\operatorname{Spec} K$, a commutative relative group law `E.L` on it, the bundle of properties `AbelianSchemePropertyBundle` (smoothness, properness, connected fibres, existence of a relative group law), all fibres of topological Krull dimension $2$, an action of $\Lambda$ by endomorphisms over the base that is unital, multiplicative and additive for the group law and satisfies the trace identity on tangent spaces at geometric points, together with the level datum `E.C`, `E.lev`. Let furthermore $f:\mathcal{A}\to\operatorname{Spec} R$ be a morphism carrying a commutative relative group law $L$ and satisfying `AbelianSchemePropertyBundle R f`, and let $g:\,$`E.A`$\,\to\mathcal{A}$ be a morphism such that the square formed by $g$, `E.f`, $f$ and $\operatorname{Spec}$ of $R\to K$ is cartesian and such that $g$ is a homomorphism: for every $T\to\operatorname{Spec} K$ and all sections $x,y$ of `E.f` over it, composing `E.L.mul` of $x$ and $y$ with $g$ agrees with $L$-multiplication of the composites, taken over $T\to\operatorname{Spec} K\to\operatorname{Spec} R$. The conclusion is that there exists a fake elliptic curve $\mathcal{E}$ over $R$ with `FakeEllipticCurve.IsPullback (algebraMap R K) 𝓔 E`: some morphism `E.A` $\to$ `𝓔.A` makes `E.f` the base change of `𝓔.f` along $R\to K$, is a homomorphism for the two group laws, commutes with the two $\Lambda$-actions, and carries sections factoring through `E.lev` to sections factoring through `𝓔.lev`.
--
--   This is the extension of all the structures of a fake elliptic curve from the generic fibre to an abelian scheme model over a discrete valuation ring, under the assumption that $N$ is invertible in $R$: the quaternionic action, the level subgroup and the numerical conditions all descend to $R$ once the abelian surface does. It is used in the construction of integral models of quaternionic Shimura curves, being invoked in the passage to full level structure over complete discrete valuation rings with finite residue field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_algebraMap_of_abelianSchemePropertyBundle_of_isPullback.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld
open CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_algebraMap_of_abelianSchemePropertyBundle_of_isPullback
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K] (hN : IsUnit ((N : ℕ) : R))
    (E : FakeEllipticCurve Λ N K)
    {𝒜 : Scheme.{u}} {f : 𝒜 ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (hcomm : L.IsCommutative)
    (h𝒜 : AbelianSchemePropertyBundle R f)
    (g : E.A ⟶ 𝒜) (hg : CategoryTheory.IsPullback g E.f f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hg_mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t' E.f),
      (E.L.mul t' x y).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ⟨x.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1) :
    ∃ 𝓔 : FakeEllipticCurve Λ N R, FakeEllipticCurve.IsPullback (algebraMap R K) 𝓔 E := by sorry
