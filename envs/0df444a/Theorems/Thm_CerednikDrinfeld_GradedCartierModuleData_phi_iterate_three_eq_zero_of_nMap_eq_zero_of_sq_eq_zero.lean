-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_phi_iterate_three_eq_zero_of_nMap_eq_zero_of_sq_eq_zero
-- name    : CerednikDrinfeld.GradedCartierModuleData.phi_iterate_three_eq_zero_of_nMap_eq_zero_of_sq_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/b0c691aa-91aa-5366-9b90-25e2daee1f2a
-- title:
--   Nilpotence of φ_L on the kernel of N(f)
-- statement:
--   Let $p$ be a prime, let $B,B'$ be commutative rings, let $j\colon \mathbb{W}(\mathbb{F}_{p^2}) \to B$ be a ring homomorphism (`Zp2 p` being the Witt vectors of `GaloisField p 2`), and let $\varphi\colon B\to B'$ be a surjective ring homomorphism whose kernel $I$ satisfies $I\cdot I=\bot$ and $px=0$ for all $x\in I$. Let $D$ be a graded Cartier module datum over $(B,j)$: a $\mathbb{W}(B)$-module $M$ with additive endomorphisms $F$ (Frobenius-semilinear), $V$ (satisfying $w\cdot Vx=V(\sigma(w)x)$ and $V(w\cdot Fx)=V(w)\cdot x$), $FV=p$, a $\mathbb{W}(B)$-linear $\varpi$ commuting with $F$ and $V$ and with $\varpi^2=p$, and a pair of complementary submodules `piece 0`, `piece 1` each of $F,V,\varpi$ shifting the index by $1$; assume $D$ is special, i.e. it admits a homogeneous $V$-basis $\gamma_0,\gamma_1$ (every $x$ uniquely $\sum_i [c_i]\gamma_i+Vy$) and is $V$-adically complete. Let $D'$ be such a datum over $(B',\varphi\circ j)$, likewise special, and let $f\colon M\to M'$ be a base change along $\varphi$: semilinear for `WittVector.map φ`, compatible with $F$, $V$, $\varpi$ and the grading, and carrying some homogeneous $V$-basis of $D$ to one of $D'$. Let $L\colon M\to N(M)$ be a canonical $L$-map, where $N(M)=(M\times M^{(\sigma)})/\langle (Vx,-\varpi x)\rangle$, and `IsCanonicalLMap` asserts that $L$ is an `IsCartierLMap` (in particular $L(Vx)$ is the class of $(\varpi x,0)$) admitting a lift to a special datum over a base $S$ surjecting onto $B$ in which multiplication by $p$ is injective. Write $N(f)\colon N(M)\to N(M')$ for the induced map and $\varphi_L$ for the endomorphism of $N(M)$ induced by $(x,y)\mapsto L x+[(y,0)]$. Then for every $z\in N(M)$ with $N(f)(z)=0$ one has $N(f)(\varphi_L z)=0$ and $\varphi_L^3(z)=0$.
--
--   This is the nilpotence statement for $\varphi_L$ on the kernel of $N(M)\to N(M')$ for a square-zero thickening annihilated by $p$, in the Cartier-theoretic study of special formal $\mathcal{O}_D$-modules underlying the Čerednik–Drinfel'd uniformisation (Boutot–Carayol II, Prop. 3.12); the exponent $3$ is explicit here, and a one-step vanishing is false. It is used to prove that $N(f)$ composed with the relevant map is a bijection on the appropriate subsets, in [`CerednikDrinfeld.GradedCartierModuleData.bijOn_nMap_eta_of_sq_eq_zero_of_mul_eq_zero`](thm.html#CerednikDrinfeld.GradedCartierModuleData.bijOn_nMap_eta_of_sq_eq_zero_of_mul_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_phi_iterate_three_eq_zero_of_nMap_eq_zero_of_sq_eq_zero.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.phi_iterate_three_eq_zero_of_nMap_eq_zero_of_sq_eq_zero
    (p : ℕ) [Fact p.Prime] {B B' : Type} [CommRing B] [CommRing B']
    (j : CerednikDrinfeld.Zp2 p →+* B) (φ : B →+* B') (hφ : Function.Surjective φ)
    (hI2 : RingHom.ker φ * RingHom.ker φ = ⊥) (hIp : ∀ x ∈ RingHom.ker φ, (p : B) * x = 0)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule)
    (D' : CerednikDrinfeld.GradedCartierModuleData p B' (φ.comp j)) (hD' : D'.IsSpecialCartierModule)
    (f : D.M →+ D'.M) (hf : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong φ D D' f)
    (L : D.M →+ D.NMod) (hL : D.IsCanonicalLMap L)
    (z : D.NMod) (hz : D.nMap D' f hf.2.2.1 hf.2.2.2.1 z = 0) :
    D.nMap D' f hf.2.2.1 hf.2.2.2.1 (D.phi L hL.isCartierLMap.map_verschiebung z) = 0 ∧
      D.phi L hL.isCartierLMap.map_verschiebung
        (D.phi L hL.isCartierLMap.map_verschiebung (D.phi L hL.isCartierLMap.map_verschiebung z)) = 0 := by sorry
