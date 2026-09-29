-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_existsUnique_comp_eq_nMap_comp_and_isCartierLMap_of_surjective_of_isSpecialCartierModule
-- name    : CerednikDrinfeld.GradedCartierModuleData.existsUnique_comp_eq_nMap_comp_and_isCartierLMap_of_surjective_of_isSpecialCartierModule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/f8d6bdd4-6757-5eb1-9917-830ff6f4fa3e
-- title:
--   Unique descent of an L-map along a surjective base change
-- statement:
--   Let $p$ be a prime, let $S$ and $B$ be commutative rings, let $j_S\colon W(\mathbb F_{p^2})\to S$ be a ring homomorphism (here `Zp2 p` is $W(\mathbb F_{p^2})$), and let $\varphi\colon S\to B$ be a surjective ring homomorphism. Let `Dl` be graded Cartier module data over $(S,j_S)$, that is, a $W(S)$-module $\tilde M$ with additive $F$, $V$, a $W(S)$-linear $\Pi$ and a decomposition into two pieces satisfying the usual semilinearity, $FV=p$, $\Pi^2=p$, commutation and degree-shift rules; assume `Dl.IsSpecialCartierModule`, i.e. $\tilde M$ admits a homogeneous $V$-basis $(\gamma_0,\gamma_1)$ (every element is uniquely $\sum_i[a_i]\gamma_i+Vy$) and is $V$-adically complete. Let `D` be such data over $(B,\varphi\circ j_S)$, likewise special, and let $f\colon\tilde M\to M$ be additive and a base change along $\varphi$: it is $W(\varphi)$-semilinear, commutes with $F$, $V$ and $\Pi$, preserves the two pieces, and carries some homogeneous $V$-basis of $\tilde M$ to one of $M$. Let $\tilde L\colon\tilde M\to N(\tilde M)$ be additive and a Cartier $L$-map: $\tilde L(w\cdot x)=\sigma(w)\cdot\tilde L(x)$, $\tilde L(Vx)$ is the class of $(\Pi x,0)$, and $\lambda\circ\tilde L=F$; here $N(\cdot)$ is the quotient of $M\times\Sigma$ by the submodule `nRel`, with $\Sigma$ the module $M$ with scalars twisted by the Witt Frobenius. Then there is exactly one additive $L\colon M\to N(M)$ with $L\circ f=N(f)\circ\tilde L$, where $N(f)$ is the map `nMap` induced by $f$ on these quotients, and with $L$ again a Cartier $L$-map.
--
--   This is the descent step in the construction of the canonical $L$-map attached to a special formal module: the $L$-map on a special graded Cartier module over a lift $S$ pushes forward uniquely along a surjection $S\to B$. It is used in producing an $L$-map over an arbitrary base, in the existence statement for canonical $L$-maps along base changes, and in the bijectivity of the comparison map $\eta$ in the nilpotent case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_existsUnique_comp_eq_nMap_comp_and_isCartierLMap_of_surjective_of_isSpecialCartierModule.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.existsUnique_comp_eq_nMap_comp_and_isCartierLMap_of_surjective_of_isSpecialCartierModule
    (p : ℕ) [Fact p.Prime] {S B : Type} [CommRing S] [CommRing B]
    (jS : CerednikDrinfeld.Zp2 p →+* S) (φ : S →+* B) (hφ : Function.Surjective φ)
    (Dl : CerednikDrinfeld.GradedCartierModuleData p S jS) (hDl : Dl.IsSpecialCartierModule)
    (D : CerednikDrinfeld.GradedCartierModuleData p B (φ.comp jS)) (hD : D.IsSpecialCartierModule)
    (f : Dl.M →+ D.M) (hf : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong φ Dl D f)
    (Ll : Dl.M →+ Dl.NMod) (hLl : Dl.IsCartierLMap Ll) :
    ∃! L : D.M →+ D.NMod,
      (∀ x : Dl.M, L (f x) = Dl.nMap D f hf.2.2.1 hf.2.2.2.1 (Ll x)) ∧ D.IsCartierLMap L := by sorry
