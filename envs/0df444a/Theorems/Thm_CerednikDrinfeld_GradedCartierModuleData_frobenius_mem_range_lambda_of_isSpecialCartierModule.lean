-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_frobenius_mem_range_lambda_of_isSpecialCartierModule
-- name    : CerednikDrinfeld.GradedCartierModuleData.frobenius_mem_range_lambda_of_isSpecialCartierModule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/9746c0e1-36ef-5e8f-a893-33f983eebb93
-- title:
--   Frobenius lands in Pi M + VM for special Cartier modules
-- statement:
--   Let $p$ be a prime, let $B$ be a commutative ring, and let $j : \mathbb{W}(\mathbb{F}_{p^2}) \to B$ be a ring homomorphism, where $\mathbb{W}(\mathbb{F}_{p^2})$ denotes the Witt vectors of the field with $p^2$ elements. Let $D$ be a graded Cartier module datum over $(B,j)$: a module $M$ over the Witt ring $\mathbb{W}(B)$ equipped with additive endomorphisms $F$ (`frobenius`) and $V$ (`verschiebung`), a $\mathbb{W}(B)$-linear endomorphism $\Pi$ (`varpi`), and two submodules $M_0, M_1$ (`piece`) that are complementary, subject to the axioms $F(w\cdot x) = \sigma(w)\cdot F x$, $w\cdot Vx = V(\sigma(w)\cdot x)$, $V(w\cdot Fx) = V(w)\cdot x$, $F(Vx) = p\,x$, $\Pi V = V\Pi$, $\Pi F = F\Pi$, $\Pi^2 = p$, and $F$, $V$, $\Pi$ each shifting the grading by $1$. Assume $D$ is special, i.e. there is a homogeneous $V$-basis $\gamma_0 \in M_0$, $\gamma_1 \in M_1$ (every $x \in M$ is uniquely of the form $\sum_i [c_i]\gamma_i + Vm$ with $c_i \in B$ Teichmüller-lifted and $m \in M$) and $M$ is $V$-adically complete (every sequence $(x_m)$ in $M$ admits a unique $s$ with $s \equiv \sum_{m<N} V^m x_m$ modulo $V^N M$ for all $N$). Then for every $x \in M$, $Fx$ lies in the image of the $\mathbb{W}(B)$-linear map $\lambda_D$ on $N(D)$ induced by $(m,m') \mapsto \Pi m + V m'$; that is, $Fx \in \Pi M + VM$.
--
--   This is the existence half of the construction of the Cartier map $L_M = \lambda_M^{-1} \circ F$ for a special formal module, as in Boutot–Carayol II (3.8)(a). Combined with injectivity of $\lambda_M$ over a $p$-torsion-free base it yields the unique factorisation of $F$ through $\lambda_M$, used by [`CerednikDrinfeld.GradedCartierModuleData.existsUnique_isCartierLMap_of_isSpecialCartierModule_of_torsionFree`](thm.html#CerednikDrinfeld.GradedCartierModuleData.existsUnique_isCartierLMap_of_isSpecialCartierModule_of_torsionFree).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_frobenius_mem_range_lambda_of_isSpecialCartierModule.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.frobenius_mem_range_lambda_of_isSpecialCartierModule
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule) (x : D.M) :
    D.frobenius x ∈ LinearMap.range D.lambda := by sorry
