-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_nsmul_eq_zero_of_lambda_eq_zero_of_cast_eq_zero
-- name    : CerednikDrinfeld.GradedCartierModuleData.nsmul_eq_zero_of_lambda_eq_zero_of_cast_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/f983935c-e89a-59ff-ada5-8f99dca43a2c
-- title:
--   Kernel of λ on N(M) is killed by p
-- statement:
--   Let $p$ be a prime, $B$ a commutative ring in which $p=0$, and $j$ a ring homomorphism from $W(\mathbb{F}_{p^2})$, the Witt vectors of the field with $p^2$ elements, to $B$. Let $D$ be a graded Cartier module datum over $(B,j)$: an abelian group $M$ with a module structure over the Witt vectors $W(B)$, additive endomorphisms $F$ (`frobenius`) and $V$ (`verschiebung`), a $W(B)$-linear endomorphism $\Pi$ (`varpi`), and a pair of submodules `piece 0`, `piece 1` which are complementary and are interchanged by $F$, $V$ and $\Pi$, subject to $F(wx)=\sigma(w)F(x)$, $wV(x)=V(\sigma(w)x)$, $V(wF(x))=V_{W}(w)x$, $F(V(x))=px$, $\Pi V=V\Pi$, $\Pi F=F\Pi$ and $\Pi^{2}=p$, where $\sigma$ and $V_{W}$ are the Frobenius and Verschiebung of $W(B)$. Let $N(M)$ be the quotient of $M\times M^{\sigma}$ (the second factor carrying the $W(B)$-structure twisted by $\sigma$) by the image of the map $m\mapsto (V m,-\Pi m)$, and let $\lambda:N(M)\to M$ be the $W(B)$-linear map induced by $(x_{1},x_{2})\mapsto \Pi x_{1}+V x_{2}$. The assertion is that every $z\in N(M)$ with $\lambda(z)=0$ satisfies $p\cdot z=0$.
--
--   This is the $p$-torsion statement for $\ker\lambda$ used in the Cerednik–Drinfeld uniformisation, in the form of Boutot–Carayol's lemma on the modified Cartier module $N(M)$. It is invoked in the comparison of $\eta$-maps, where the discrepancy between two such maps lands in $\ker\lambda$ and is thereby seen to be annihilated by $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_nsmul_eq_zero_of_lambda_eq_zero_of_cast_eq_zero.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.nsmul_eq_zero_of_lambda_eq_zero_of_cast_eq_zero
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B) (hp : (p : B) = 0)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (z : D.NMod) (hz : D.lambda z = 0) :
    p • z = 0 := by sorry
