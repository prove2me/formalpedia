-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullbackVia_fstHom_comp_eq_of_isPullbackVia_map_smul_of_levelIff
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullbackVia_fstHom_comp_eq_of_isPullbackVia_map_smul_of_levelIff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/bed1b09e-78cd-5e43-8706-643cac6ca2c4
-- title:
--   Scaling ε↦ cε preserves reduction, compatibly with comparison maps
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, naturals $N,m$, and a field $k$. Let $u$ be a fake elliptic curve with full level over $k$ and $v,w$ two such objects over the dual numbers $\mathrm{DualNumber}\,k=k[\varepsilon]$ (each a pair consisting of a `FakeEllipticCurve` over the base together with a `FullLevel` structure of level $m$, whose datum `P` is a distinguished section of the curve over the base). Let $c\in k$. Suppose given $gv : u.A \to v.A$ exhibiting $u$ as base change of $v$ along $\varepsilon\mapsto 0$, in the project's sense `IsPullbackVia`: the square with $gv$, the two structure maps and $\mathrm{Spec}$ of $\varepsilon\mapsto0$ is cartesian, $gv$ carries the relative group law to the relative group law on $T$-points, commutes with the action of every $x\in\Lambda$, and sends $T$-points factoring through the level map $u.\mathrm{lev}$ to points whose composite with $gv$ factors through $v.\mathrm{lev}$; suppose also $(u.P)\circ gv = \mathrm{Spec}(\varepsilon\mapsto0)\circ (v.P)$. Suppose likewise $h : w.A\to v.A$ exhibits $w$ as base change of $v$ along $\sigma_c:\varepsilon\mapsto c\varepsilon$ (same four clauses), with $(w.P)\circ h = \mathrm{Spec}(\sigma_c)\circ (v.P)$, and assume in addition the converse level clause for $h$: for every $T$-point $P$ of $w.A$ over any $t':T\to\mathrm{Spec}\,k[\varepsilon]$, if $P\circ h$ factors through $v.\mathrm{lev}$ then $P$ factors through $w.\mathrm{lev}$. Then there exists $gw : u.A\to w.A$ exhibiting $u$ as base change of $w$ along $\varepsilon\mapsto0$ in the same sense, satisfying $(u.P)\circ gw = \mathrm{Spec}(\varepsilon\mapsto0)\circ (w.P)$, and with $gw\circ h = gv$.
--
--   This is the compatibility needed to transport a first-order deformation along the scaling automorphism $\varepsilon\mapsto c\varepsilon$ of $k[\varepsilon]$ while keeping its reduction to $u$ identified on the nose: the twisted object $w$ still reduces to $u$, and the comparison maps form a commuting triangle over $u$. It feeds the construction of the $k$-module structure on the tangent space of the moduli problem of fake elliptic curves with full level structure, used in the existence statement for scalar multiplication on that tangent space in characteristic $p$ over an algebraically closed field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullbackVia_fstHom_comp_eq_of_isPullbackVia_map_smul_of_levelIff.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullbackVia_fstHom_comp_eq_of_isPullbackVia_map_smul_of_levelIff
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m : ℕ}
    (k : Type) [Field k]
    (u : FakeEllipticCurve.WithFullLevel Λ N m k)
    (v w : FakeEllipticCurve.WithFullLevel Λ N m (DualNumber k)) (c : k)
    (gv : u.1.A ⟶ v.1.A) (hgv : FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.fstHom k k k).toRingHom v.1 u.1 gv)
    (hgvP : (u.2.P).1 ≫ gv = Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ (v.2.P).1)
    (h : w.1.A ⟶ v.1.A)
    (hh : FakeEllipticCurve.IsPullbackVia
      (TrivSqZeroExt.map (R' := k) (c • (LinearMap.id : k →ₗ[k] k))).toRingHom v.1 w.1 h)
    (hhP : (w.2.P).1 ≫ h =
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (R' := k) (c • (LinearMap.id : k →ₗ[k] k))).toRingHom) ≫ (v.2.P).1)

    (hhlev : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (DualNumber k))) (P : SchemeHomOver t' w.1.f),
      (∃ P₀ : T ⟶ v.1.C, P₀ ≫ v.1.lev = P.1 ≫ h) → FactorsThrough w.1.lev P) :
    ∃ gw : u.1.A ⟶ w.1.A,
      FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.fstHom k k k).toRingHom w.1 u.1 gw ∧
      (u.2.P).1 ≫ gw = Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ (w.2.P).1 ∧
      gw ≫ h = gv := by sorry
