-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isIsogenyPair_comp_eq_of_isPullbackVia_of_isPullbackVia
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isIsogenyPair_comp_eq_of_isPullbackVia_of_isPullbackVia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/7bac8f49-4c96-5700-8ac4-d5e7d12db74f
-- title:
--   Base change of degree-d isogeny pairs of fake elliptic curves
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, a commutative ring $B$, two objects $E,E_f$ of type `FakeEllipticCurve` $\Lambda$ $N$ $B$ (abelian schemes of relative dimension $2$ over $\operatorname{Spec} B$ with commutative relative group law, a $\Lambda$-action satisfying the trace condition, and level data), and a natural number $d$. Let $q : E.A \to E_f.A$ and $q' : E_f.A \to E.A$ form an `IsIsogenyPair` of degree $d$: both lie over $\operatorname{Spec} B$ ($q \circ E_f.f = E.f$ and $q' \circ E.f = E_f.f$ in diagrammatic order), each is additive on $T$-valued points for the relative group laws, each commutes with the $\Lambda$-actions ($E.\mathrm{act}\,x$ followed by $q$ equals $q$ followed by $E_f.\mathrm{act}\,x$, and symmetrically for $q'$), and whenever the image of $d$ in $\mathbb{H}[\mathbb{Q},a,b]$ lies in $\Lambda$ one has $q$ followed by $q'$ equal to $E.\mathrm{act}\,d$ and $q'$ followed by $q$ equal to $E_f.\mathrm{act}\,d$. Let $\varphi : B \to L$ be a ring homomorphism and let $E_L, E_{f,L}$ be fake elliptic curves over $L$ with morphisms $g : E_L.A \to E.A$ and $g_f : E_{f,L}.A \to E_f.A$ exhibiting each as a pull-back along $\varphi$ in the sense of `IsPullbackVia`: the square formed by $g$, $E_L.f$, $E.f$ and $\operatorname{Spec}$ of $\varphi$ is cartesian, $g$ carries the group law on $T$-points of $E_L$ to that of $E$ after base change of the structure morphism, $g$ intertwines the $\Lambda$-actions, and any $T$-point of $E_L$ factoring through $E_L.\mathrm{lev}$ has its composite with $g$ factoring through $E.C$ via $E.\mathrm{lev}$; likewise for $g_f$ relative to $E_f$. The conclusion: there exist $q_L : E_L.A \to E_{f,L}.A$ and $q'_L : E_{f,L}.A \to E_L.A$ with $q_L$ followed by $g_f$ equal to $g$ followed by $q$, with $q'_L$ followed by $g$ equal to $g_f$ followed by $q'$, and with $(q_L,q'_L)$ an `IsIsogenyPair` of degree $d$ between $E_L$ and $E_{f,L}$.
--
--   This is the base-change functoriality of $\Lambda$-linear isogeny pairs: an isogeny pair of degree $d$ between fake elliptic curves over $B$ induces one, compatible with the comparison morphisms, between their pull-backs along any ring map $B \to L$. It is used in the fine Čerednik–Drinfeld comparison to transport Atkin–Lehner and Hecke isogeny pairs onto the local pieces over which rigidifications and formal coordinates are available.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isIsogenyPair_comp_eq_of_isPullbackVia_of_isPullbackVia.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMRigidification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Quaternion CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isIsogenyPair_comp_eq_of_isPullbackVia_of_isPullbackVia
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {B : Type} [CommRing B] {E Ef : FakeEllipticCurve Λ N B} {d : ℕ}
    (q : E.A ⟶ Ef.A) (q' : Ef.A ⟶ E.A) (hqq' : FakeEllipticCurve.IsIsogenyPair d E Ef q q')
    {L : Type} [CommRing L] (φ : B →+* L)
    {EL EfL : FakeEllipticCurve Λ N L}
    (g : EL.A ⟶ E.A) (hg : FakeEllipticCurve.IsPullbackVia φ E EL g)
    (gf : EfL.A ⟶ Ef.A) (hgf : FakeEllipticCurve.IsPullbackVia φ Ef EfL gf) :
    ∃ (qL : EL.A ⟶ EfL.A) (qL' : EfL.A ⟶ EL.A), qL ≫ gf = g ≫ q ∧ qL' ≫ g = gf ≫ q' ∧
      FakeEllipticCurve.IsIsogenyPair d EL EfL qL qL' := by sorry
