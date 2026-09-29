-- Prove2me | Theorems.Thm_AlgebraicCurve_traceDiff_inv_smul_D_eq_inv_norm_smul_D_norm
-- name    : AlgebraicCurve.traceDiff_inv_smul_D_eq_inv_norm_smul_D_norm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/7584121c-0ee8-51fd-b46e-9f44d59367a4
-- title:
--   Trace of dlog h equals dlog of the norm
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ algebras over $K$, $F'$ an algebra over $F$, the three structures forming a scalar tower over $K$, and $F'$ separable over $F$; let $h \in F'$. Here `traceDiff K F F'` denotes the $F$-linear map $\Omega_{F'/K} \to \Omega_{F/K}$ obtained as follows: if there exists an $F$-linear $t : \Omega_{F'/K} \to \Omega_{F/K}$ with $t\bigl(y \cdot (\text{base-change of } \omega)\bigr) = \mathrm{Tr}_{F'/F}(y) \cdot \omega$ for all $y \in F'$ and all $\omega \in \Omega_{F/K}$, then such a $t$ is chosen, and otherwise the zero map. The assertion is the identity in $\Omega_{F/K}$
--   $$\mathrm{traceDiff}_{K,F,F'}\bigl(h^{-1} \cdot d_{K/F'}h\bigr) \;=\; N_{F'/F}(h)^{-1} \cdot d_{K/F}\bigl(N_{F'/F}(h)\bigr),$$
--   where $d_{K/F'}$ and $d_{K/F}$ are the universal $K$-derivations into the respective modules of Kähler differentials and $N_{F'/F}$ is the algebra norm. No finiteness hypothesis on $F'/F$ is imposed: where $F'$ fails to be finite free over $F$, the norm is $1$ and the trace is $0$, and the identity degenerates accordingly; likewise for $h = 0$ both sides vanish, since inversion is extended by $0^{-1} = 0$.
--
--   This is the norm–trace compatibility of logarithmic differentials: the trace of differentials sends $\mathrm{dlog}\,h$ to $\mathrm{dlog}\,N_{F'/F}(h)$. It is used in the divisor-theoretic comparison [`AlgebraicCurve.Divisor.correspondence_eq_ord_norm_and_dlog_norm_eq_traceAlong_pullbackAlong`](thm.html#AlgebraicCurve.Divisor.correspondence_eq_ord_norm_and_dlog_norm_eq_traceAlong_pullbackAlong) and in the computation of the differential correspondence attached to the Hecke operators on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_traceDiff_inv_smul_D_eq_inv_norm_smul_D_norm.lean

import Definitions.Def_ModularCurve_QExpansionDiff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.traceDiff_inv_smul_D_eq_inv_norm_smul_D_norm (K F F' : Type*) [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsSeparable F F'] (h : F') : traceDiff K F F' (h⁻¹ • KaehlerDifferential.D K F' h) = (Algebra.norm F h)⁻¹ • KaehlerDifferential.D K F (Algebra.norm F h) := by sorry
