-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_nsmul_nMap_mem_eta_of_mem_eta_of_cast_eq_zero
-- name    : CerednikDrinfeld.GradedCartierModuleData.nsmul_nMap_mem_eta_of_mem_eta_of_cast_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/05b044d0-7dc5-5ff9-be4a-d01f43cc912e
-- title:
--   η is functorial after multiplication by p
-- statement:
--   Let $p$ be a prime, let $B$ and $B'$ be commutative rings equipped with ring homomorphisms $j \colon \mathbb{W}(\mathbb{F}_{p^2}) \to B$ and $j' \colon \mathbb{W}(\mathbb{F}_{p^2}) \to B'$ (here [`CerednikDrinfeld.Zp2 p`](def/CerednikDrinfeld_SpecialFormalModule.html#L17) is the ring of Witt vectors of the field with $p^2$ elements), and suppose $p = 0$ in $B'$. Let $D$ be a graded Cartier module datum over $(B,j)$ and $D'$ one over $(B',j')$: each consists of a module $M$ over $\mathbb{W}(B)$ (resp. $\mathbb{W}(B')$), additive endomorphisms $F$ and $V$ and a linear endomorphism $\Pi$ of $M$, and a pair of complementary submodules `piece 0`, `piece 1`, subject to $F(w\cdot x) = \sigma(w)\cdot F x$, $w \cdot Vx = V(\sigma(w)\cdot x)$, $V(w \cdot Fx) = V(w)\cdot x$, $F\circ V = p$, $\Pi V = V\Pi$, $\Pi F = F\Pi$, $\Pi^2 = p$, and the requirement that $F$, $V$, $\Pi$ each shift the grading by $1$. Let $f \colon D.M \to D'.M$ be an additive map commuting with $F$, with $V$ and with $\Pi$. Let $L \colon D.M \to D.\mathrm{NMod}$ and $L' \colon D'.M \to D'.\mathrm{NMod}$ be additive maps satisfying `IsCartierLMap`, i.e. each is $\sigma$-semilinear, carries $Vx$ to the class of $(\Pi x, 0)$, and satisfies $\lambda \circ L = F$; here $\mathrm{NMod}$ is the quotient of $M \times \Sigma$ (with $\Sigma = M$ carrying the $\mathbb{W}$-structure twisted by Frobenius) by the image of `nRelMap`, and $\lambda$ sends the class of $(x,y)$ to $\Pi x + V y$. Then for every $z$ in $D.\mathrm{eta}\,L$, that is every $z \in D.\mathrm{NMod}$ fixed by the additive endomorphism `D.phi L`, the element $p \cdot (\mathrm{nMap}\,f)(z)$ lies in $D'.\mathrm{eta}\,L'$, where $\mathrm{nMap}\,f \colon D.\mathrm{NMod} \to D'.\mathrm{NMod}$ is the map induced by $f \times f$ using the compatibility of $f$ with $V$ and $\Pi$. No compatibility between $L'\circ f$ and $(\mathrm{nMap}\,f)\circ L$ is assumed.
--
--   The subgroup $\eta(L)$ of $\phi_L$-fixed points of $N(M)$ is the lattice-type invariant attached to a Cartier datum in the Čerednik–Drinfel'd uniformisation; this statement records that, over a base where $p$ vanishes, $\eta$ is functorial for maps commuting with $F$, $V$ and $\Pi$ once one multiplies by $p$, without requiring any compatibility of the chosen $L$-maps. It is used in the construction and comparison of rigidifications of Cartier quadruples and in the computation of the lattice map attached to a translate datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_nsmul_nMap_mem_eta_of_mem_eta_of_cast_eq_zero.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.nsmul_nMap_mem_eta_of_mem_eta_of_cast_eq_zero
    (p : ℕ) [Fact p.Prime] {B B' : Type} [CommRing B] [CommRing B']
    {j : CerednikDrinfeld.Zp2 p →+* B} {j' : CerednikDrinfeld.Zp2 p →+* B'} (hp : (p : B') = 0)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (D' : CerednikDrinfeld.GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M)
    (hF : ∀ x, f (D.frobenius x) = D'.frobenius (f x))
    (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x))
    (L : D.M →+ D.NMod) (hL : D.IsCartierLMap L)
    (L' : D'.M →+ D'.NMod) (hL' : D'.IsCartierLMap L')
    (z : D.NMod) (hz : z ∈ D.eta L hL.map_verschiebung) :
    p • D.nMap D' f hV hPi z ∈ D'.eta L' hL'.map_verschiebung := by sorry
