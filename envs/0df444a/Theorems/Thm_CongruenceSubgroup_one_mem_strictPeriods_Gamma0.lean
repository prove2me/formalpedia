-- Prove2me | Theorems.Thm_CongruenceSubgroup_one_mem_strictPeriods_Gamma0
-- name    : CongruenceSubgroup.one_mem_strictPeriods_Gamma0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/78b85fa4-bdd5-57a2-975e-2c775a128376
-- title:
--   1 is a strict period of Γ₀(N)
-- statement:
--   For every natural number $N$, the real number $1$ belongs to the additive subgroup of strict periods, `Subgroup.strictPeriods`, of the image of $\Gamma_0(N)$ in $\mathrm{GL}_2(\mathbb{R})$. Here $\Gamma_0(N) \subseteq \mathrm{SL}_2(\mathbb{Z})$ is `CongruenceSubgroup.Gamma0 N`, the subgroup of integral matrices of determinant $1$ whose lower-left entry is divisible by $N$, and the ambient group is its image under the homomorphism `Matrix.SpecialLinearGroup.mapGL ℝ` which sends an element of $\mathrm{SL}_2(\mathbb{Z})$ to the corresponding invertible real $2 \times 2$ matrix; for a subgroup $\Gamma$ of $\mathrm{GL}_2(\mathbb{R})$, Mathlib's `Subgroup.strictPeriods` is the additive subgroup of those $x \in \mathbb{R}$ for which the upper triangular unipotent matrix with off-diagonal entry $x$ lies in $\Gamma$. Thus the assertion is exactly that the translation $\begin{pmatrix}1&1\\0&1\end{pmatrix}$ lies in the image of $\Gamma_0(N)$, with no hypothesis on $N$ (the degenerate value $N = 0$ is included).
--
--   This is the statement that the cusp $\infty$ of $\Gamma_0(N)$ has width dividing $1$, i.e. that forms of level $\Gamma_0(N)$ are invariant under $\tau \mapsto \tau + 1$ and so admit a $q$-expansion in $q = e^{2\pi i \tau}$. It is the side condition required by Mathlib's $q$-expansion theory, and is invoked throughout the treatment of $q$-coefficients of modular and cusp forms of level $\Gamma_0(N)$, for instance in the normalisation of Hecke eigenforms and in the construction of ring homomorphisms out of Hecke algebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CongruenceSubgroup_one_mem_strictPeriods_Gamma0.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CongruenceSubgroup.one_mem_strictPeriods_Gamma0 (N : ℕ) : (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 N)).strictPeriods := by sorry
