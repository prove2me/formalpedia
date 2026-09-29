-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_isCompl_nPiece_zero_one
-- name    : CerednikDrinfeld.GradedCartierModuleData.isCompl_nPiece_zero_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/0120e172-01c3-5060-9eb7-6b52a1a8ea70
-- title:
--   Gradedness of the modified Cartier module N(M)
-- statement:
--   Fix a natural number $p$ that is prime, a commutative ring $B$, and a ring homomorphism $j$ from $\mathbb{Z}_{p^2} =$ `WittVector p (GaloisField p 2)` to $B$, and let $D$ be a graded Cartier module datum over $(B,j)$: thus $D$ consists of a type $M$ with the structure of a module over the Witt vectors $\mathbb{W} =$ `WittVector p B`, additive endomorphisms $F$ (`frobenius`) and $V$ (`verschiebung`) of $M$ and a $\mathbb{W}$-linear endomorphism $\Pi$ (`varpi`), together with two $\mathbb{W}$-submodules `piece 0`, `piece 1` of $M$, subject to: $F(w\cdot x)=\sigma(w)\cdot F x$, $w\cdot Vx = V(\sigma(w)\cdot x)$, $V(w\cdot Fx)=V(w)\cdot x$ for $w\in\mathbb{W}$ (with $\sigma$, $V$ the Witt vector Frobenius and Verschiebung), $F\circ V = p$, $\Pi V = V\Pi$, $\Pi F = F\Pi$, $\Pi^2 = p$, the two pieces being complementary submodules of $M$, and each of $V$, $F$, $\Pi$ carrying `piece i` into `piece (i+1)` with indices in `Fin 2`. The assertion is that, in the lattice of additive subgroups of the quotient $N(M) = (M\times \Sigma)/\,$`nRel`, the two subgroups `D.nPiece 0` and `D.nPiece 1` — the images under the quotient map `D.nMk` of the subgroups of pairs both of whose coordinates lie in `piece 0`, respectively `piece 1` — are complementary: they intersect in $0$ and their sum is all of $N(M)$.
--
--   This is the degree bookkeeping showing that the modified Cartier module $N(M) = (M\oplus M^{\sigma})/\{(Vm,-\Pi m)\}$ inherits the $\mathbb{Z}/2$-grading of $M$, as in the $p$-adic uniformisation of Shimura curves. It is used throughout the subsequent treatment of Cartier–Drinfeld lattices, for instance to place transported sections in the degree-zero piece and in the statements about canonical maps and about $\eta$-pieces of formal $\mathcal{O}_D$-modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_isCompl_nPiece_zero_one.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.isCompl_nPiece_zero_one
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) :
    IsCompl (D.nPiece 0) (D.nPiece 1) := by sorry
