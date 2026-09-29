-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_id_comp_eq_of_isPullbackVia_of_bijective_of_level_one
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_id_comp_eq_of_isPullbackVia_of_bijective_of_level_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/859cdce2-4ef4-5dc8-a0c1-aad1b392344a
-- title:
--   Level-one fake elliptic curves have one deformation over k
-- statement:
--   Fix rationals $a,b$ and a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a field $k$, a commutative ring $S$ and a ring homomorphism $\rho : S \to k$ which is bijective as a map of sets. Let $E_0$ be a fake elliptic curve over $k$ of level $N=1$ and let $E,E'$ be fake elliptic curves over $S$ of level $N=1$; here a fake elliptic curve consists of a scheme $A$ with a structure morphism $f$ to $\operatorname{Spec}$ of the base, a commutative relative group law on $f$, the smoothness/properness/connected-fibres bundle, two-dimensional fibres, an action of $\Lambda$ by endomorphisms over the base satisfying the additivity, multiplicativity and trace axioms, and a level datum $\mathrm{lev}$ from an auxiliary scheme $C$. Suppose given $g : E_0.A \to E.A$ and $g' : E_0.A \to E'.A$ each satisfying `IsPullbackVia` for $\rho$, i.e. the square formed by $g$, $E_0.f$, $E.f$ and $\operatorname{Spec}(\rho)$ (respectively with $E'$) is a pullback, the morphism carries the relative group law on points over any base change to that of the target over $\operatorname{Spec}(\rho)$, it intertwines the $\Lambda$-actions ($E_0.\mathrm{act}\,x$ followed by $g$ equals $g$ followed by $E.\mathrm{act}\,x$ for all $x \in \Lambda$), and any point of $E_0$ factoring through $E_0.\mathrm{lev}$ has its composite with $g$ factoring through the target's $\mathrm{lev}$. Then there exists $h : E.A \to E'.A$ satisfying the same four conditions with respect to the identity homomorphism of $S$, and such that $g$ followed by $h$ equals $g'$.
--
--   This is the statement that the deformation problem for a level-one fake elliptic curve $E_0$ has exactly one point over a base isomorphic to the residue field itself, with isomorphisms of deformations expressed as pullbacks along the identity compatible with the chosen map from $E_0$; it is the ground-level hypothesis of the Schlessinger-type comparison used in the Čerednik–Drinfeld part of the project. It feeds the uniqueness statement for pullbacks over power-series bases, [`CerednikDrinfeld.QM.FakeEllipticCurve.forall_existsUnique_isPullbackVia_powerSeries_of_tower_nontrivial_of_isAlgClosed_residueField_one_of_ne`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.forall_existsUnique_isPullbackVia_powerSeries_of_tower_nontrivial_of_isAlgClosed_residueField_one_of_ne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_id_comp_eq_of_isPullbackVia_of_bijective_of_level_one.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_id_comp_eq_of_isPullbackVia_of_bijective_of_level_one
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (k : Type) [Field k] (S : Type) [CommRing S] (ρ : S →+* k) (hρ : Function.Bijective ρ)
    (E₀ : FakeEllipticCurve Λ 1 k)
    (E : FakeEllipticCurve Λ 1 S) (g : E₀.A ⟶ E.A) (hg : FakeEllipticCurve.IsPullbackVia ρ E E₀ g)
    (E' : FakeEllipticCurve Λ 1 S) (g' : E₀.A ⟶ E'.A) (hg' : FakeEllipticCurve.IsPullbackVia ρ E' E₀ g') :
    ∃ h : E.A ⟶ E'.A, FakeEllipticCurve.IsPullbackVia (RingHom.id S) E' E h ∧ g ≫ h = g' := by sorry
