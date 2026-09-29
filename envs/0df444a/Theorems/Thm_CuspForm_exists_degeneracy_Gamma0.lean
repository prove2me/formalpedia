-- Prove2me | Theorems.Thm_CuspForm_exists_degeneracy_Gamma0
-- name    : CuspForm.exists_degeneracy_Gamma0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/cd45b6a6-d6e5-5d9d-90de-20b47b250822
-- title:
--   Degeneracy map f(τ)↦ f(dτ) from Γ₀(M) to Γ₀(N)
-- statement:
--   Let $k$ be an integer, let $M$, $N$, $d$ be natural numbers with $N$ nonzero, and assume $d\,M \mid N$. Let $f$ be a cusp form of weight $k$ for the congruence subgroup $\Gamma_0(M)$ (viewed, as in Mathlib, as a subgroup of $\mathrm{GL}_2(\mathbb{R})$ via $\mathrm{SL}_2(\mathbb{Z})$). Here [`ModularForm.heckeDiagMatrix d`](def/ModularForm_HeckeOperator.html#L21) denotes the element of $\mathrm{GL}_2(\mathbb{R})$ equal to the identity when $d = 0$ and to the upper triangular matrix $\begin{pmatrix} d & 0\\ 0 & 1\end{pmatrix}$ (with nonzero determinant $d$) otherwise; note that the divisibility hypothesis together with $N \neq 0$ forces $d \neq 0$. The assertion is that there exists a cusp form $g$ of weight $k$ for $\Gamma_0(N)$ whose underlying function on the upper half-plane is exactly $\tau \mapsto f\bigl(\mathrm{heckeDiagMatrix}(d) \cdot \tau\bigr)$, i.e. $g(\tau) = f(d\tau)$, with no normalising scalar in the conclusion. Thus holomorphy, the weight-$k$ invariance under $\Gamma_0(N)$ and vanishing at all cusps hold for $\tau \mapsto f(d\tau)$.
--
--   This is the degeneracy (level-raising) map $V_d \colon S_k(\Gamma_0(M)) \to S_k(\Gamma_0(N))$, $f \mapsto f(d\tau)$, for $d\,M \mid N$, which produces the oldforms at level $N$ coming from level $M$. It is used in the project to move cusp forms to larger level, for instance in the construction of normalised eigenforms at multiplied level and in identities for eta products.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_degeneracy_Gamma0.lean

import Definitions.Def_ModularForm_HeckeOperator
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.exists_degeneracy_Gamma0 {k : ℤ} {M N d : ℕ} [NeZero N] (hd : d * M ∣ N) (f : CuspForm (CongruenceSubgroup.Gamma0 M) k) : ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) k, ⇑g = fun τ ↦ f (ModularForm.heckeDiagMatrix d • τ) := by sorry
