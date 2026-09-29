-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_of_exists_comp_eq_comp_of_isPullbackVia
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_comp_of_isPullbackVia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/2d486328-4714-5dd3-94db-0faa566db6dd
-- title:
--   Level subscheme of a pullback is the full pullback
-- statement:
--   Fix a natural number $N$, rationals $a,b$ and a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$. Let $S_0$ and $\bar B$ be commutative rings, $A_0$ a fake elliptic curve of type $(\Lambda,N)$ over $S_0$, $\psi_b : S_0 \to \bar B$ a ring homomorphism, $A_b$ a fake elliptic curve of type $(\Lambda,N)$ over $\bar B$, and $g_A : A_b.A \to A_0.A$ a morphism of schemes satisfying `IsPullbackVia`, that is: the square formed by $g_A$, the structure morphisms $A_b.f$ and $A_0.f$ and $\operatorname{Spec}(\psi_b)$ is a pullback; $g_A$ carries the relative group law of $A_b$ to that of $A_0$ on $T$-points; $g_A$ intertwines the $\Lambda$-actions, $A_b.\mathrm{act}(x)$ followed by $g_A$ equals $g_A$ followed by $A_0.\mathrm{act}(x)$ for all $x \in \Lambda$; and every $T$-point of $A_b$ factoring through $A_b.\mathrm{lev}$ has its image under $g_A$ factoring through $A_0.\mathrm{lev}$. Let $T$ be a scheme, $t' : T \to \operatorname{Spec}\bar B$, and $P$ a $T$-point of $A_b$ over $t'$, i.e. $P : T \to A_b.A$ with $P$ followed by $A_b.f$ equal to $t'$. Assume there is $P_0 : T \to A_0.C$ with $P_0$ followed by $A_0.\mathrm{lev}$ equal to $P$ followed by $g_A$. Then $P$ factors through $A_b.\mathrm{lev}$: there is $P_0' : T \to A_b.C$ with $P_0'$ followed by $A_b.\mathrm{lev}$ equal to $P$. The proof uses only the pullback square and the forward level clause of `IsPullbackVia`, not its group-law or $\Lambda$-equivariance clauses.
--
--   This supplies the converse of the level clause built into `IsPullbackVia`: for a fake elliptic curve obtained by base change, the level subscheme is the full pullback of the level subscheme downstairs, so that membership in the level structure can be tested after pushing forward to $A_0$. It is used throughout the rigidification arguments for fake elliptic curves, in particular when comparing level structures across base changes and Atkin–Lehner quotients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_of_exists_comp_eq_comp_of_isPullbackVia.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_comp_of_isPullbackVia
    {N : ℕ} {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    {S₀ : Type} [CommRing S₀] (A₀ : FakeEllipticCurve Λ N S₀)
    {Bb : Type} [CommRing Bb] (ψb : S₀ →+* Bb)
    (Ab : FakeEllipticCurve Λ N Bb) (gA : Ab.A ⟶ A₀.A) (hAb : FakeEllipticCurve.IsPullbackVia ψb A₀ Ab gA)
    {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of Bb)) (P : SchemeHomOver t' Ab.f)
    (hP : ∃ P₀ : T ⟶ A₀.C, P₀ ≫ A₀.lev = P.1 ≫ gA) :
    FactorsThrough Ab.lev P := by sorry
