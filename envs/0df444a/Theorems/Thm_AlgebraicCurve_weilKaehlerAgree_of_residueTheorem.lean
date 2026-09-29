-- Prove2me | Theorems.Thm_AlgebraicCurve_weilKaehlerAgree_of_residueTheorem
-- name    : AlgebraicCurve.weilKaehlerAgree_of_residueTheorem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/58343ca3-7efc-50ce-9bea-170c73496430
-- title:
--   Weil–Kähler agreement from the residue theorem
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and impose: a canonical local residue datum at every place (the class `HasCanonicalLocalResidueKStar` assigns to each place $v$ — a valuation subring of $F$ containing the image of $K$, not all of $F$, and a principal ideal ring — a local residue map whose value on $(\pi_v^{n+1})^{-1}$ vanishes for every $n\ge 1$, $\pi_v$ a uniformizer); `HasCanonicalDivisor`, i.e. every nonzero $\omega\in\Omega_{F/K}$ admits a divisor $D$ (a finitely supported $\mathbb{Z}$-valued function on places) with $D(v)=\operatorname{ord}_v(\omega)$ for all $v$; that $v.\mathrm{dCoord}$ spans $\Omega_{F/K}$ over $F$ at every place $v$; that $\Omega_{F/K}$ is nontrivial; `HasSeparableResidue`, i.e. the $K$-linear trace $\mathrm{Algebra.trace}\,K\,(\text{residue field of }v)$ is nonzero for each $v$; and that there is at least one place. Assume the residue theorem `ResidueTheorem K F`: whenever principal divisors exist, the functional $\lambda_\omega=$`weilOfKaehler`$(\omega)$ — sending an adele $\alpha$ to the finite sum over places of the local Kähler residue terms of $\omega$ against $\alpha$ — kills every diagonal (constant) adele coming from $f\in F$. The conclusion is `WeilKaehlerAgree K F`: assuming principal divisors exist, for every $\omega\neq 0$ the functional $\lambda_\omega$ is nonzero, lies in $\Omega(D_\omega)$, the annihilator of the space of adeles bounded by the canonical divisor $D_\omega=$`canonicalDivisorOf`$(\omega)$, and $D_\omega$ is maximal with this property: any divisor $D$ with $\lambda_\omega\in\Omega(D)$ satisfies $D\le D_\omega$.
--
--   This is the reduction, in the adelic treatment of the Riemann–Roch theorem for function fields (Stichtenoth I.5), of the identification of Weil differentials with Kähler differentials to the global residue theorem: the residue functional attached to a nonzero $\omega$ is a nonzero Weil differential whose associated divisor is exactly the canonical divisor of $\omega$. It is invoked for the function field of the modular curve over $\mathbb{C}$ in [`ModularCurve.weilKaehlerAgree_modularFunctionFieldC`](thm.html#ModularCurve.weilKaehlerAgree_modularFunctionFieldC), and feeds the Riemann–Roch input of the wider development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_weilKaehlerAgree_of_residueTheorem.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_WeilOfKaehler

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicCurve

theorem weilKaehlerAgree_of_residueTheorem {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]] [HasSeparableResidue K F] [Nonempty (Place K F)]
    (hRT : ResidueTheorem K F) : WeilKaehlerAgree K F := by sorry
