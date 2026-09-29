-- Prove2me | Theorems.Thm_CuspForm_exists_coe_eq_heckeU
-- name    : CuspForm.exists_coe_eq_heckeU
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/2af4db20-2887-5f8f-8045-f62ee3a634bb
-- title:
--   Uₚ preserves cusp forms on Γ₀(N) for p ∣ N
-- statement:
--   Let $N$ be a natural number with $N \neq 0$, let $k \in \mathbb{Z}$, and let $f$ be a cusp form of weight $k$ for the congruence subgroup $\Gamma_0(N)$, viewed as a subgroup of $\mathrm{GL}_2(\mathbb{R})$. Let $p$ be a natural number dividing $N$ (no primality is assumed; note that $p \mid N$ and $N \neq 0$ force $p \neq 0$). The assertion is that the function $\mathtt{heckeU}\,k\,p$ applied to the underlying function of $f$ is again the underlying function of a cusp form of the same weight and level: there exists $g$, a cusp form of weight $k$ for $\Gamma_0(N)$, whose coercion to a function on the upper half-plane equals [`ModularForm.heckeU k p ⇑f`](def/ModularForm_HeckeOperator.html#L93). Here [`ModularForm.heckeU k p`](def/ModularForm_HeckeOperator.html#L93) is defined on arbitrary functions $F \colon \mathbb{H} \to \mathbb{C}$ by $\sum_{j=0}^{p-1} F \mid_k \gamma_{p,j}$, where $\gamma_{p,j}$ is the image in $\mathrm{GL}_2(\mathbb{R})$ of the upper triangular matrix $\begin{pmatrix} 1 & j \\ 0 & p\end{pmatrix}$ (and the identity when $p = 0$); no normalising power of $p$ is inserted. Thus the unnormalised operator $U_p$ maps $S_k(\Gamma_0(N))$ into itself when $p \mid N$.
--
--   This is the statement that $U_p$ is a well-defined endomorphism of the space of cusp forms of weight $k$ on $\Gamma_0(N)$ at a divisor $p$ of the level, the classical $U_p$ operator of the theory of modular forms of level $N$. It is used in the construction of normalised eigenforms and in the integrality and congruence statements about $q$-expansion coefficients that enter the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_coe_eq_heckeU.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.exists_coe_eq_heckeU {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) {p : ℕ} (hpN : p ∣ N) : ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) k, ⇑g = ModularForm.heckeU k p ⇑f := by sorry
