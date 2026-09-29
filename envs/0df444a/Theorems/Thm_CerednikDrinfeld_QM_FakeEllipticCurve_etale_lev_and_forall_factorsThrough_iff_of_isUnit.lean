-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_etale_lev_and_forall_factorsThrough_iff_of_isUnit
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.etale_lev_and_forall_factorsThrough_iff_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/f0cf7f5c-ff14-51e3-8b2b-53d6b410f2cb
-- title:
--   Level subscheme is étale, and membership is geometric
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, and a commutative ring $S$, and let $E$ be a fake elliptic curve of type `FakeEllipticCurve` $\Lambda$ $N$ $S$: a scheme `E.A` with a morphism `E.f : E.A ⟶ Spec (CommRingCat.of S)` carrying a commutative relative group law `E.L` (functorial multiplication, unit and inverse on $T$-points over $S$), satisfying the abelian-scheme property bundle (smooth, proper, connected fibres, a group law exists), with all fibres of topological Krull dimension $2$, an additive and multiplicative action of $\Lambda$ on `E.A` over $S$ whose traces on tangent spaces are the reduced traces, together with the level data `E.lev : E.C ⟶ E.A`. Assume the image of $N$ in $S$ is a unit. Then, first, the composite of `E.lev` with `E.f` is étale; and second, for every scheme $T$, every morphism $t : T \to \operatorname{Spec} S$ and every $T$-point $P$ of `E.A` over $t$ (a morphism $P \to$ `E.A` composing with `E.f` to $t$), the point $P$ factors as $P_0$ followed by `E.lev` for some $P_0 : T \to$ `E.C` if and only if the $N$-fold iterated `E.L`-multiple of $P$ equals the unit section `E.L.one t` and, for every algebraically closed field $k$, every ring homomorphism $s_k : S \to k$ and every $\tau : \operatorname{Spec} k \to T$ with $\tau$ followed by $t$ equal to $\operatorname{Spec}(s_k)$, the point $\tau$ followed by $P$ factors through `E.lev`.
--
--   This records that, when $N$ is invertible on the base, the level subscheme `E.C` is étale over $\operatorname{Spec} S$ — it sits as an open and closed subgroup scheme of the finite étale $N$-torsion — so that for an $N$-torsion point membership in `E.C` is detected on geometric points alone. It rests on the finiteness and étaleness of the $N$-torsion kernel [`CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_and_etale_schemeKerStr_of_isUnit`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_and_etale_schemeKerStr_of_isUnit), and is used in the comparison and descent arguments for level structures on fake elliptic curves, including the pullback and isomorphism statements for curves with extra or full level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_etale_lev_and_forall_factorsThrough_iff_of_isUnit.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open NeronModelInfra hiding schemeHomOverComp
open GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.etale_lev_and_forall_factorsThrough_iff_of_isUnit
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (E : FakeEllipticCurve Λ N S) (hN : IsUnit ((N : ℕ) : S)) :
    Etale (E.lev ≫ E.f) ∧
    ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      FactorsThrough E.lev P ↔
        nsmulPt E.L t N P = E.L.one t ∧
        ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (τ : Spec (CommRingCat.of k) ⟶ T)
          (hτ : τ ≫ t = geomPoint k sk), FactorsThrough E.lev (schemeHomOverComp τ hτ P) := by sorry
