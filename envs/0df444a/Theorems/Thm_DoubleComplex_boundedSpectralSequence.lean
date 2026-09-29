-- Prove2me | Theorems.Thm_DoubleComplex_boundedSpectralSequence
-- name    : DoubleComplex.boundedSpectralSequence
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/8f7a0a87-7770-51b0-abda-6a65387d4aef
-- title:
--   Convergence data for bounded double complexes
-- statement:
--   The theorem asserts the proposition [`DoubleComplex.BoundedSpectralSequence`](def/AlgebraicGeometry_DoubleComplex.html#L224), namely: for every commutative ring $R$ and every $D : \mathrm{DoubleComplex.Bounded}\ R$ — that is, a bigraded family of $R$-modules $C^{p,q}$ indexed by $p,q \in \mathbb{N}$, together with $R$-linear maps $d_H : C^{p,q} \to C^{p+1,q}$ and $d_V : C^{p,q} \to C^{p,q+1}$ satisfying $d_H \circ d_H = 0$, $d_V \circ d_V = 0$ and the commuting-square identity $d_V \circ d_H = d_H \circ d_V$, and a bound $N \in \mathbb{N}$ such that $C^{p,q}$ is a subsingleton whenever $N \le p$ or $N \le q$ — the type $\mathrm{Convergence}\ R\ (E_2^{I} D)\ (H_{\mathrm{tot}} D)\ N$ is nonempty, where `E₂I D` is the bigraded family of $R$-modules attached to $D$ playing the role of the $E_2$-page of the first spectral sequence, and $H_{\mathrm{tot}}(D)^n = \ker(d_{\mathrm{tot}}^n)/B^n$ is the $n$-th cohomology of the total complex of $D$. Inhabiting `Convergence` means giving: subquotients $E_\infty^{p,q}$ of $E_2^{I}(D)^{p,q}$ (objects of `SubQuot`, each with submodules `.Z`, `.B` and carrier), with $(E_\infty^{p,0}).Z = \top$; for each $p$ a monotone filtration $B_\bullet : \mathrm{Fin}(N+1) \to$ submodules of $E_2^{I}(D)^{p,0}$ with $B_0 = \bot$, $B_N = (E_\infty^{p,0}).B$, each successive quotient $B_{i+1}/B_i$ being linearly isomorphic to the carrier of some subquotient of some $E_2^{I}(D)^{p',q'}$ with $q' \ge 1$; and for each $n$ a monotone filtration $F_\bullet : \mathrm{Fin}(N+2) \to$ submodules of $H_{\mathrm{tot}}(D)^n$ with $F_0 = \bot$, $F_{N+1} = \top$, such that for every $p \le N$ one has $F_{p+1}/F_p \cong (E_\infty^{p,0})$ inside $H_{\mathrm{tot}}(D)^p$.
--
--   This is the convergence statement for the first spectral sequence ${}'E_2^{p,q} = H^p_h H^q_v(C) \Rightarrow H^{p+q}(\mathrm{Tot}\,C)$ of a bounded first-quadrant double complex, packaged in the restricted form actually needed: only the bottom row $q = 0$, the edge filtration of the total cohomology and the comparison of the remaining graded pieces with subquotients of terms in rows $q \ge 1$. It is used in the finiteness argument for Čech cohomology of $\mathcal{O}$-module presheaves over an integral base, via [`AlgebraicGeometry.OModulePresheaf.cechFinite_unit_of_isIntegral_of_ih`](thm.html#AlgebraicGeometry.OModulePresheaf.cechFinite_unit_of_isIntegral_of_ih).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DoubleComplex_boundedSpectralSequence.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem DoubleComplex.boundedSpectralSequence : DoubleComplex.BoundedSpectralSequence.{u} := by sorry
