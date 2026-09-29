-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCartierLMap_nMap_apply_eq_zero_of_apply_eq_zero
-- name    : CerednikDrinfeld.GradedCartierModuleData.IsCartierLMap.nMap_apply_eq_zero_of_apply_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/cdc529ca-72a8-5c52-891f-4d8d20e6f6e2
-- title:
--   An L-map carries ker f into ker N(f)
-- statement:
--   Fix a prime $p$, commutative rings $S$ and $B$, a ring homomorphism $jS$ from $\mathbb{W}(\mathbb{F}_{p^2})$ to $S$ and a ring homomorphism $\varphi\colon S\to B$. Let $Dl$ be graded Cartier module data for $p$ over $S$ along $jS$ and $D$ such data over $B$ along $\varphi\circ jS$; each consists of a module over the Witt vectors of its base ring equipped with additive maps $F$, $V$, a linear $\Pi$ and a decomposition into two complementary pieces satisfying the usual Cartier relations. Let $f\colon Dl.M\to D.M$ be additive and assume `IsBaseChangeAlong`: $f$ is semilinear along `WittVector.map` $\varphi$, commutes with $F$, $V$ and $\Pi$, carries the piece of index $i$ into the piece of index $i$, and there is a family $\gamma\colon \mathrm{Fin}\,2\to Dl.M$ which is a homogeneous $V$-basis of $Dl$ and whose image under $f$ is a homogeneous $V$-basis of $D$. Let $Ll\colon Dl.M\to Dl.\mathrm{NMod}$ be additive with `IsCartierLMap`: $Ll(w\cdot x)=\sigma(w)\cdot Ll(x)$, $Ll(Vx)$ is the class of $(\Pi x,0)$, and $\lambda(Ll\,x)=Fx$. Then for every $x\in Dl.M$ with $f(x)=0$, the map $N(f)$ induced by $f$ on the quotients $\mathrm{NMod}$ annihilates $Ll(x)$.
--
--   This is the one-step statement that an $L$-map on the source respects the kernel of a base-change map, so that it descends to the target: it is the well-definedness part of the construction of the $L$-map on a quotient in Cartier theory for special formal $\mathcal{O}_D$-modules. It is used in the existence-and-uniqueness statement `existsUnique_comp_eq_nMap_comp_and_isCartierLMap_of_surjective_of_isSpecialCartierModule`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_IsCartierLMap_nMap_apply_eq_zero_of_apply_eq_zero.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.IsCartierLMap.nMap_apply_eq_zero_of_apply_eq_zero
    (p : ℕ) [Fact p.Prime] {S B : Type} [CommRing S] [CommRing B]
    (jS : CerednikDrinfeld.Zp2 p →+* S) (φ : S →+* B)
    (Dl : CerednikDrinfeld.GradedCartierModuleData p S jS)
    (D : CerednikDrinfeld.GradedCartierModuleData p B (φ.comp jS))
    (f : Dl.M →+ D.M) (hf : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong φ Dl D f)
    (Ll : Dl.M →+ Dl.NMod) (hLl : Dl.IsCartierLMap Ll)
    (x : Dl.M) (hx : f x = 0) :
    Dl.nMap D f hf.2.2.1 hf.2.2.2.1 (Ll x) = 0 := by sorry
