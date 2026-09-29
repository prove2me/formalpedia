-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCartierLMap_comp_eq_nMap_comp_of_forall_apply_basis_eq
-- name    : CerednikDrinfeld.GradedCartierModuleData.IsCartierLMap.comp_eq_nMap_comp_of_forall_apply_basis_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/567c2e1b-d11d-5efe-9a4a-f40e8487c1ea
-- title:
--   Relative Cartier L-map determined by its values on a V-basis
-- statement:
--   Let $p$ be a prime, let $S$ and $B$ be commutative rings, and let $\varphi\colon S\to B$ be a ring homomorphism, where $S$ and $B$ are equipped with ring homomorphisms $j_S, j$ from $W(\mathbb{F}_{p^2})$ (the Witt vectors of the field with $p^2$ elements). Let $D_S$ and $D$ be graded Cartier module data over $S$ and over $B$ respectively: each consists of a module $M$ over $W(\,\cdot\,)$ together with additive endomorphisms $F$ and $V$, a linear $\Pi$, and a pair of submodules $\mathrm{piece}\,0,\mathrm{piece}\,1$ forming complements, subject to the usual semilinearity and commutation identities ($F(wx)=\sigma(w)F(x)$, $wV(x)=V(\sigma(w)x)$, $V(wF x)=V(w)x$, $FV=p$, $\Pi$ commuting with $F$ and $V$, $\Pi^2=p$, and $F,V,\Pi$ shifting the grading by $1$). Let $h\colon D_S.M\to D.M$ be an additive map which is a base change along $\varphi$ in the sense of `IsBaseChangeAlong'`: $h$ is semilinear for $W(\varphi)$, commutes with $F$, $V$ and $\Pi$, preserves the two graded pieces, and carries some homogeneous $V$-basis of $D_S$ to a homogeneous $V$-basis of $D$. Let $L_S\colon D_S.M\to D_S.\mathrm{NMod}$ and $K\colon D.M\to D.\mathrm{NMod}$ be additive maps which are Cartier $L$-maps, i.e. $\sigma$-semilinear, satisfying $L(Vx)=[(\Pi x,0)]$ in the quotient $\mathrm{NMod}$, and $\lambda\circ L=F$. Let $\gamma\colon \mathrm{Fin}\,2\to D_S.M$ be a homogeneous $V$-basis, that is, $\gamma_i\in D_S.\mathrm{piece}\,i$ and every $x\in D_S.M$ is uniquely of the form $\sum_i [c_i]\gamma_i+V(y)$ with $c\in S^2$, $y\in D_S.M$. Write $N(h)$ for the induced additive map $D_S.\mathrm{NMod}\to D.\mathrm{NMod}$ built from $h$ using its compatibility with $V$ and $\Pi$. If $K(h(\gamma_i))=N(h)(L_S(\gamma_i))$ for $i=0,1$, then $K(h(x))=N(h)(L_S(x))$ for every $x\in D_S.M$.
--
--   This is the relative form of the observation that a Cartier $L$-map is determined by its values on a homogeneous $V$-basis, transported along a base change of graded Cartier module data. It is the uniqueness and naturality tool used in comparing $L$-maps pushed forward from different lifts, and it is cited in the treatment of canonical $L$-maps (torsion-free and nilpotent cases).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_IsCartierLMap_comp_eq_nMap_comp_of_forall_apply_basis_eq.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.IsCartierLMap.comp_eq_nMap_comp_of_forall_apply_basis_eq
    (p : ℕ) [Fact p.Prime] {S B : Type} [CommRing S] [CommRing B]
    {jS : CerednikDrinfeld.Zp2 p →+* S} {j : CerednikDrinfeld.Zp2 p →+* B} (φ : S →+* B)
    (DS : CerednikDrinfeld.GradedCartierModuleData p S jS) (D : CerednikDrinfeld.GradedCartierModuleData p B j)
    (h : DS.M →+ D.M) (hh : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' φ DS D h)
    (LS : DS.M →+ DS.NMod) (hLS : DS.IsCartierLMap LS)
    (K : D.M →+ D.NMod) (hK : D.IsCartierLMap K)
    (γ : Fin 2 → DS.M) (hγ : DS.IsHomogeneousVBasis γ)
    (hKγ : ∀ i : Fin 2, K (h (γ i)) = DS.nMap D h hh.2.2.1 hh.2.2.2.1 (LS (γ i))) :
    ∀ x : DS.M, K (h x) = DS.nMap D h hh.2.2.1 hh.2.2.2.1 (LS x) := by sorry
