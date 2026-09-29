-- Prove2me | Theorems.Thm_CuspForm_eq_zero_of_coe_add_slash_heckeDiagMatrix_eq_zero
-- name    : CuspForm.eq_zero_of_coe_add_slash_heckeDiagMatrix_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/534a6f4c-f4d4-53cf-a0ac-bd99a52b82f6
-- title:
--   Joint vanishing of x+y∣_kdiag(q',1) for cusp forms
-- statement:
--   Let $R$ be a non-zero natural number, let $q'$ be a prime not dividing $R$, and let $k$ be an integer. Write $\Gamma_0(R)$ for the usual congruence subgroup of $\mathrm{SL}_2(\mathbb{Z})$, viewed through the canonical map as a subgroup of $\mathrm{GL}_2(\mathbb{R})$, and let $x$ and $y$ be cusp forms of weight $k$ for that subgroup. Let $\delta =$ `heckeDiagMatrix` $q'$ be the element of $\mathrm{GL}_2(\mathbb{R})$ given by the upper triangular matrix $\begin{pmatrix} q' & 0 \\ 0 & 1\end{pmatrix}$ (the definition returns the identity when the natural number argument is $0$, which does not occur here since $q'$ is prime), and let $\mid[k]$ denote the weight-$k$ slash action on functions $\mathfrak{H} \to \mathbb{C}$. The hypothesis is the equality of functions on the upper half-plane $$x + y\mid[k]\,\delta = 0,$$ where $x$ and $y$ are identified with their underlying functions $\mathfrak{H} \to \mathbb{C}$. The conclusion is that both $x = 0$ and $y = 0$ in the space of weight-$k$ cusp forms for $\Gamma_0(R)$.
--
--   This is the characteristic-zero injectivity statement for the pair of degeneracy maps $S_k(\Gamma_0(R)) \oplus S_k(\Gamma_0(R)) \to S_k(\Gamma_0(Rq'))$ given by inclusion and by rescaling $\tau \mapsto q'\tau$, in the Ihara-style form used in congruence relations between modular forms of level $R$ and level $Rq'$. It is cited by [`FreyPackage.ModMCarrier.levelInclusionLin_add_rescaleLin_eq_zero`](thm.html#FreyPackage.ModMCarrier.levelInclusionLin_add_rescaleLin_eq_zero), the corresponding vanishing statement for the linear maps attached to the Frey package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_eq_zero_of_coe_add_slash_heckeDiagMatrix_eq_zero.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CongruenceSubgroup ModularForm
open scoped ModularForm UpperHalfPlane MatrixGroups

theorem CuspForm.eq_zero_of_coe_add_slash_heckeDiagMatrix_eq_zero
    {R q' : ℕ} [NeZero R] (hq' : q'.Prime) (hq'R : ¬ q' ∣ R) (k : ℤ)
    (x y : CuspForm ((Gamma0 R : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    (h : (⇑x : ℍ → ℂ) + ((⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix q') = 0) :
    x = 0 ∧ y = 0 := by sorry
