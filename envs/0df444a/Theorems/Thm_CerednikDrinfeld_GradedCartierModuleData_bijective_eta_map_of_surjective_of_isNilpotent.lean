-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_bijective_eta_map_of_surjective_of_isNilpotent
-- name    : CerednikDrinfeld.GradedCartierModuleData.bijective_eta_map_of_surjective_of_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/ecd05eeb-df28-50b2-9000-70e5e896fa75
-- title:
--   Bijectivity of N(f) on η under nilpotent thickenings
-- statement:
--   Fix a prime $p$ and write $\mathbb{Z}_{p^2}$ for $W(\mathbb{F}_{p^2})$. Let $B$, $B'$ be commutative rings, $j\colon \mathbb{Z}_{p^2}\to B$ a ring homomorphism, and $\varphi\colon B\to B'$ a surjective ring homomorphism whose kernel is a nilpotent ideal and is killed by some power $p^b$ (there is $b$ with $p^b x=0$ for all $x\in\ker\varphi$). Let $D$ be graded Cartier module data over $(p,B,j)$ and $D'$ over $(p,B',\varphi\circ j)$, both special, i.e. each admits a homogeneous $V$-basis $\gamma\colon \mathrm{Fin}\,2\to M$ with $\gamma_i$ in the $i$-th piece and every element uniquely of the form $\sum_i \tau(c_i)\gamma_i+V y$, and each is $V$-adically complete. Let $f\colon D.M\to D'.M$ be additive and a base change along $\varphi$: it is $\varphi$-semilinear for the Witt-vector actions, commutes with $F$, $V$ and $\varpi$, preserves the two pieces, and carries some homogeneous $V$-basis of $D$ to one of $D'$. Let $L$, $L'$ be canonical $L$-maps for $D$, $D'$ (Cartier $L$-maps, so $L(Vx)$ is the class of $(\varpi x,0)$ in $N$, which descend from Cartier $L$-maps over a ring without $p$-torsion surjecting onto the base), compatible in the sense $L'\circ f=N(f)\circ L$. Then the induced additive map $N(f)\colon N(D)\to N(D')$ on the quotients $N=(M\times M^{\sigma})/\mathrm{nRel}$ restricts to a bijection from $\eta(L)=\ker(\phi_L-\mathrm{id})$ onto $\eta(L')=\ker(\phi_{L'}-\mathrm{id})$.
--
--   This is the rigidity property of Drinfeld's invariant $\eta$ under nilpotent thickenings of the base, as in Boutot–Carayol II (3.14): the fixed points of $\phi_L$ are insensitive to a nilpotent ideal killed by a power of $p$. It is obtained from the case $I^2=0$, $pI=0$ by induction along a filtration of the kernel, and is used for the corresponding statements about special formal modules, in particular for descent of $\eta$-classes along localisations and surjections with nilpotent kernel.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_bijective_eta_map_of_surjective_of_isNilpotent.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.bijective_eta_map_of_surjective_of_isNilpotent
    (p : ℕ) [Fact p.Prime] {B B' : Type} [CommRing B] [CommRing B']
    (j : CerednikDrinfeld.Zp2 p →+* B) (φ : B →+* B') (hφ : Function.Surjective φ)
    (hI : IsNilpotent (RingHom.ker φ)) (hIp : ∃ b : ℕ, ∀ x ∈ RingHom.ker φ, (p : B) ^ b * x = 0)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule)
    (D' : CerednikDrinfeld.GradedCartierModuleData p B' (φ.comp j)) (hD' : D'.IsSpecialCartierModule)
    (f : D.M →+ D'.M) (hf : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong φ D D' f)
    (L : D.M →+ D.NMod) (hL : D.IsCanonicalLMap L)
    (L' : D'.M →+ D'.NMod) (hL' : D'.IsCanonicalLMap L')
    (hLL' : ∀ x : D.M, L' (f x) = D.nMap D' f hf.2.2.1 hf.2.2.2.1 (L x)) :
    Set.BijOn (D.nMap D' f hf.2.2.1 hf.2.2.2.1)
      (D.eta L hL.isCartierLMap.map_verschiebung : Set D.NMod)
      (D'.eta L' hL'.isCartierLMap.map_verschiebung : Set D'.NMod) := by sorry
