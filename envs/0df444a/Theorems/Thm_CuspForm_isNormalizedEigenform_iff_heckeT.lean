-- Prove2me | Theorems.Thm_CuspForm_isNormalizedEigenform_iff_heckeT
-- name    : CuspForm.isNormalizedEigenform_iff_heckeT
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/e2ea40f7-d7af-5267-a9a7-bef8555698b1
-- title:
--   Normalized eigenforms as simultaneous Tₚ, Uₚ eigenfunctions
-- statement:
--   Let $N$ be a nonzero natural number and let $f$ be a cusp form of weight $2$ for $\Gamma_0(N)$. Write $a_n =$ [`ModularFormClass.qCoeff f n`](def/FLTPrelim_Modularity.html#L19), the $n$-th coefficient of the $q$-expansion of $f$ with respect to the period $1$. The assertion is that the structure [`CuspForm.IsNormalizedEigenform`](def/FLTPrelim_Modularity.html#L28) holds for $f$ — that is, $a_1 = 1$, $a_{mn} = a_m a_n$ for all coprime $m, n$, $a_{p^{r+2}} = a_p a_{p^{r+1}} - p\,a_{p^{r}}$ for every prime $p$ with $p \nmid N$ and all $r$, and $a_{p^{r+2}} = a_p a_{p^{r+1}}$ for every prime $p$ with $p \mid N$ and all $r$ — if and only if $a_1 = 1$ and, for every prime $p$: if $p \nmid N$ then [`ModularForm.heckeT 2 p`](def/ModularForm_HeckeOperator.html#L96) applied to the underlying function of $f$ equals $a_p \cdot f$, and if $p \mid N$ then [`ModularForm.heckeU 2 p`](def/ModularForm_HeckeOperator.html#L93) applied to that function equals $a_p \cdot f$. Here `heckeU 2 p` is $\sum_{j<p} f \mid_2 \begin{pmatrix} 1 & j \\ 0 & p\end{pmatrix}$ and `heckeT 2 p` adds to this the single term $f \mid_2 \begin{pmatrix} p & 0 \\ 0 & 1\end{pmatrix}$; both identities are equalities of functions on the upper half-plane.
--
--   This is the standard dictionary between the recursive, multiplicative normalisation of the $q$-expansion coefficients of a weight-$2$ cusp form on $\Gamma_0(N)$ and the property of being a simultaneous eigenfunction of the Hecke operators $T_p$ ($p \nmid N$) and $U_p$ ($p \mid N$) with eigenvalue the corresponding coefficient. It is used to convert statements about Hecke eigenvectors in spaces of cusp forms — such as the existence of normalized eigenforms attached to maximal or prime ideals of the Hecke algebra, and the Atkin–Lehner behaviour of newforms — into the coefficient recursions required by the Frey-curve argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_isNormalizedEigenform_iff_heckeT.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.isNormalizedEigenform_iff_heckeT {N : ℕ} [NeZero N] (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) : f.IsNormalizedEigenform ↔ (ModularFormClass.qCoeff f 1 = 1 ∧ ∀ p : ℕ, p.Prime → ((¬ p ∣ N → ModularForm.heckeT 2 p ⇑f = ModularFormClass.qCoeff f p • ⇑f) ∧ (p ∣ N → ModularForm.heckeU 2 p ⇑f = ModularFormClass.qCoeff f p • ⇑f))) := by sorry
