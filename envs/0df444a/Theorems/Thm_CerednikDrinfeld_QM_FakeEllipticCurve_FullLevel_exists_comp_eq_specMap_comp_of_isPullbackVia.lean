-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_comp_eq_specMap_comp_of_isPullbackVia
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_comp_eq_specMap_comp_of_isPullbackVia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/5bbd0bf4-39b6-5fd7-a523-3a9f01aa5907
-- title:
--   Full level structures pull back along base change
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, natural numbers $N$ and $m$, commutative rings $S,S'$ and a ring homomorphism $\varphi\colon S\to S'$. Let $E$ be a fake elliptic curve with $\Lambda$-action and level datum of index $N$ over $S$, let $E'$ be one over $S'$, and let $g\colon E'.A\to E.A$ be a morphism of schemes with `FakeEllipticCurve.IsPullbackVia` $\varphi$ $E$ $E'$ $g$, that is: the square formed by $g$, the structure morphisms $E'.f$, $E.f$ and $\mathrm{Spec}\,\varphi$ is cartesian; for every scheme $T$, every $t'\colon T\to\mathrm{Spec}\,S'$ and all points $P,Q$ of $E'$ over $t'$, the underlying morphism of their product composed with $g$ is the product over $t'$ followed by $\mathrm{Spec}\,\varphi$ of their composites with $g$; $E'.\mathrm{act}\,x$ followed by $g$ equals $g$ followed by $E.\mathrm{act}\,x$ for every $x\in\Lambda$; and any point of $E'$ factoring through $E'.\mathrm{lev}$ has its composite with $g$ factoring through $E.\mathrm{lev}$. Let $P$ be a full level-$m$ structure on $E$: a section of $E.f$ over $\mathrm{Spec}\,S$ which is killed by $m$ for the relative group law, whose $\Lambda$-translates at every geometric point $S\to k$ ($k$ algebraically closed) exhaust the $m$-torsion points there, and whose annihilator in $\Lambda$ at every such geometric point is exactly $m\Lambda$. The conclusion is that there exists a full level-$m$ structure $P'$ on $E'$ whose underlying section, followed by $g$, equals $\mathrm{Spec}\,\varphi$ followed by the underlying section of $P$.
--
--   This is the base-change functoriality of full level-$m$ structures on fake elliptic curves, in the form of an existence statement together with the naming of the comparison identity satisfied by the transported structure. It is used throughout the rigidification step of the Čerednik–Drinfeld comparison, for instance in the results on norm-level transport and on uniqueness of full level structures over connected bases.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_comp_eq_specMap_comp_of_isPullbackVia.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_comp_eq_specMap_comp_of_isPullbackVia
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (m : ℕ)
    {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S') (g : E'.A ⟶ E.A)
    (hg : FakeEllipticCurve.IsPullbackVia φ E E' g) (P : E.FullLevel m) :
    ∃ P' : E'.FullLevel m, (P'.P).1 ≫ g = Spec.map (CommRingCat.ofHom φ) ≫ (P.P).1 := by sorry
