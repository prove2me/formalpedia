-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_existsUnique_isCartierLMap_of_isSpecialCartierModule_of_torsionFree
-- name    : CerednikDrinfeld.GradedCartierModuleData.existsUnique_isCartierLMap_of_isSpecialCartierModule_of_torsionFree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/f40877ed-5f15-5bf6-b67a-7eec914b2ebf
-- title:
--   Existence and uniqueness of L_M over p-torsion-free bases
-- statement:
--   Fix a prime $p$, a commutative ring $B$ and a ring homomorphism $j \colon \mathbb{W}(\mathbb{F}_{p^2}) \to B$ (the source being [`CerednikDrinfeld.Zp2 p`](def/CerednikDrinfeld_SpecialFormalModule.html#L17), the Witt vectors of the field with $p^2$ elements), and assume that $p$ is a non-zero-divisor in $B$, i.e. $pb = 0$ implies $b = 0$ for all $b \in B$. Let $D$ be a graded Cartier module datum over $(p, B, j)$: a $\mathbb{W}(B)$-module $M$ with additive endomorphisms $F$ (`frobenius`) and $V$ (`verschiebung`), a $\mathbb{W}(B)$-linear $\Pi$ (`varpi`), and two submodules $M_0, M_1$ forming a complementary pair, subject to $F(wx) = \sigma(w)F(x)$, $wV(x) = V(\sigma(w)x)$, $V(wF(x)) = V(w)x$, $F(V(x)) = px$, $\Pi V = V\Pi$, $\Pi F = F\Pi$, $\Pi^2 = p$, and the requirement that $V$, $F$ and $\Pi$ each carry $M_i$ into $M_{i+1}$ ($i \in \mathbb{Z}/2$). Assume $D$ is a special Cartier module, that is: there is a homogeneous $V$-basis, a pair $\gamma_0 \in M_0$, $\gamma_1 \in M_1$ such that every $x \in M$ is uniquely of the form $\sum_i [c_i]\gamma_i + V(y)$ with $c_i \in B$ (Teichmüller representatives) and $y \in M$; and $M$ is $V$-adically complete in the sense that for every sequence $(x_m)_{m \in \mathbb{N}}$ in $M$ there is exactly one $s \in M$ admitting, for each $N$, some $t$ with $s = \sum_{m < N} V^m(x_m) + V^N(t)$. The conclusion is that there is a unique additive map $L \colon M \to N(M)$ satisfying the three conditions packaged in `IsCartierLMap`, where $N(M)$ is the quotient of $M \times M^{\sigma}$ ($M^{\sigma}$ being $M$ with $\mathbb{W}(B)$ acting through Frobenius) by the submodule `D.nRel`, the range of `D.nRelMap`: namely $L(wx) = \sigma(w)L(x)$ for all $w \in \mathbb{W}(B)$ and $x \in M$, $L(V(x))$ is the class of $(\Pi x, 0)$, and $\lambda(L(x)) = F(x)$, $\lambda \colon N(M) \to M$ being the $\mathbb{W}(B)$-linear map induced by $(m, m') \mapsto \Pi m + V m'$.
--
--   This is the construction of the structural map $L_M$ attached to a special formal module in Cartier-theoretic form, in the case of a base in which $p$ is a non-zero-divisor; the general base is handled separately by lifting and pushing forward along surjections. It is used to produce the canonical $L$-map attached to a formal $\mathcal{O}_D$-module and, through uniqueness, to compare $L$-maps with maps induced by morphisms of graded Cartier modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_existsUnique_isCartierLMap_of_isSpecialCartierModule_of_torsionFree.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.existsUnique_isCartierLMap_of_isSpecialCartierModule_of_torsionFree
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (hB : ∀ b : B, (p : B) * b = 0 → b = 0)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule) :
    ∃! L : D.M →+ D.NMod, D.IsCartierLMap L := by sorry
