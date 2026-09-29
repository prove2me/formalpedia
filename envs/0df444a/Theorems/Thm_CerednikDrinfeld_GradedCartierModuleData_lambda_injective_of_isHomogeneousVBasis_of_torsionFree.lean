-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_lambda_injective_of_isHomogeneousVBasis_of_torsionFree
-- name    : CerednikDrinfeld.GradedCartierModuleData.lambda_injective_of_isHomogeneousVBasis_of_torsionFree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/dee4926b-fd3e-593e-89ba-e31ba76261e8
-- title:
--   Injectivity of λ given a homogeneous V-basis
-- statement:
--   Let $p$ be a prime, let $B$ be a commutative ring and let $j\colon \mathbb{Z}_{p^2} = W(\mathbb{F}_{p^2}) \to B$ be a ring homomorphism, where `Zp2 p` denotes the Witt vectors of the field `GaloisField p 2`. Assume that $p$ is a non-zero-divisor in $B$, i.e. $p\cdot b = 0$ implies $b = 0$ for all $b \in B$. Let $D$ be a graded Cartier module datum over $(p, B, j)$: a $W(B)$-module $M$ together with additive endomorphisms $F$ (`frobenius`) and $V$ (`verschiebung`), a $W(B)$-linear endomorphism $\Pi$ (`varpi`) and two complementary $W(B)$-submodules `piece 0`, `piece 1`, subject to $F(w\cdot x) = \sigma(w)\cdot F x$, $w\cdot Vx = V(\sigma(w)\cdot x)$, $V(w\cdot Fx) = \sigma^{-1}(w)\cdot x$ in the form `verschiebung w • x`, $FV = p$, the commutation of $\Pi$ with $F$ and $V$, $\Pi^2 = p$, and the shifting of the grading by $F$, $V$ and $\Pi$. Suppose $\gamma\colon \mathrm{Fin}\,2 \to M$ is a homogeneous $V$-basis, that is $\gamma_i \in$ `piece i` and every $x \in M$ has a unique expression $x = \sum_{i} [c_i]\cdot\gamma_i + V y$ with $(c_0,c_1) \in B^2$ and $y \in M$, where $[\,\cdot\,]$ is the Teichmüller lift. Then the $W(B)$-linear map `D.lambda` on `D.NMod`, the quotient of $M \times \Sigma$ by the submodule `nRel` (the range of `nRelMap`), induced by $(m,m') \mapsto \Pi m + V m'$ after the additive identification of $\Sigma$ with $M$, is injective.
--
--   This is the injectivity half of the comparison between a graded Cartier module and the module $N(M)$ attached to it in the Čerednik–Drinfeld uniformisation theory, as in Boutot–Carayol, chapter II; here it is proved directly for the abstract datum, assuming only the existence of a homogeneous $V$-basis and that $p$ is a non-zero-divisor, with no completeness hypothesis. It is used in the analysis of the map $\lambda$ on the graded pieces of a special formal $\mathcal{O}_D$-module, for instance in the results establishing that $\lambda$ restricts to a bijection on the relevant pieces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_lambda_injective_of_isHomogeneousVBasis_of_torsionFree.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.lambda_injective_of_isHomogeneousVBasis_of_torsionFree
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (hB : ∀ b : B, (p : B) * b = 0 → b = 0)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j)
    (γ : Fin 2 → D.M) (hγ : D.IsHomogeneousVBasis γ) :
    Function.Injective D.lambda := by sorry
