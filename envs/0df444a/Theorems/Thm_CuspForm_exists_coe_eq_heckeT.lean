-- Prove2me | Theorems.Thm_CuspForm_exists_coe_eq_heckeT
-- name    : CuspForm.exists_coe_eq_heckeT
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/124bb715-179d-577b-a42d-56d62eba02b0
-- title:
--   Tₚ preserves cusp forms on Γ₀(N) for p ∤ N
-- statement:
--   Let $N$ be a natural number, $k$ an integer, and let $f$ be a cusp form of weight $k$ for the congruence subgroup $\Gamma_0(N)$, i.e. an element of `CuspForm (CongruenceSubgroup.Gamma0 N) k` (so $f$ is slash-invariant of weight $k$ under $\Gamma_0(N)$, holomorphic on the upper half-plane, and vanishes at every cusp of $\Gamma_0(N)$). Let $p$ be a natural number which is prime and does not divide $N$. The assertion is that there exists a cusp form $g$ of weight $k$ for $\Gamma_0(N)$ whose underlying function on the upper half-plane is $\mathrm{heckeT}\,k\,p\,f$, that is, $$g = \sum_{j<p} f\mid_k \mathrm{heckeMatrix}\,p\,j \;+\; f\mid_k \begin{pmatrix} p & 0 \\ 0 & 1\end{pmatrix},$$ where $\mid_k$ is the weight-$k$ slash action of $\mathrm{GL}_2(\mathbb{R})$ on functions on the upper half-plane, the elements $\mathrm{heckeMatrix}\,p\,j$ of $\mathrm{GL}_2(\mathbb{R})$ are those entering the definition of [`ModularForm.heckeU`](def/ModularForm_HeckeOperator.html#L93), and the last matrix is [`ModularForm.heckeDiagMatrix p`](def/ModularForm_HeckeOperator.html#L21) (for $p \neq 0$ the upper triangular matrix with diagonal entries $p$ and $1$ and vanishing off-diagonal entries). Equivalently: the function $T_p f$ again satisfies the three defining conditions of a cusp form of weight $k$ on $\Gamma_0(N)$.
--
--   This is the statement that the Hecke operator $T_p$, for $p$ prime and coprime to the level, maps $S_k(\Gamma_0(N))$ into itself, so that it defines an endomorphism of the space of cusp forms. It is used in the construction of normalised eigenforms and in the study of their $q$-expansion coefficients, being cited by [`CuspForm.exists_isNormalizedEigenform`](thm.html#CuspForm.exists_isNormalizedEigenform) and [`CuspForm.IsNormalizedEigenform.exists_integralClosure_coe_eq_qCoeff`](thm.html#CuspForm.IsNormalizedEigenform.exists_integralClosure_coe_eq_qCoeff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_coe_eq_heckeT.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.exists_coe_eq_heckeT {N : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) : ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) k, ⇑g = ModularForm.heckeT k p ⇑f := by sorry
