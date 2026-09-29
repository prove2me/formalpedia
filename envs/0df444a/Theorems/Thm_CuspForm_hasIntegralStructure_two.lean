-- Prove2me | Theorems.Thm_CuspForm_hasIntegralStructure_two
-- name    : CuspForm.hasIntegralStructure_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/14abbaf4-cc9d-5afa-809d-b913856b53ac
-- title:
--   Integral structure on weight-2 cusp forms for Γ₀(N)
-- statement:
--   Let $N$ be a natural number, assumed nonzero. Consider the complex vector space $S_2(\Gamma_0(N))$ of weight-$2$ cusp forms for the congruence subgroup $\Gamma_0(N)$, and let $L \subseteq S_2(\Gamma_0(N))$ be the $\mathbb{Z}$-submodule [`CuspForm.intLattice N 2`](def/CuspForm_IntegralStructure.html#L3), defined as the $\mathbb{Z}$-span of the set of those cusp forms $f$ for which every $q$-expansion coefficient $a_n(f)$ (the coefficients [`ModularFormClass.qCoeff f n`](def/FLTPrelim_Modularity.html#L19), for all $n \in \mathbb{N}$) is the image in $\mathbb{C}$ of a rational integer. The theorem asserts the predicate [`CuspForm.HasIntegralStructure N 2`](def/CuspForm_IntegralStructure.html#L6), which says that the $\mathbb{C}$-span of the underlying set of $L$ is the whole space, i.e. $\operatorname{span}_{\mathbb{C}} L = \top$ in the lattice of $\mathbb{C}$-submodules of $S_2(\Gamma_0(N))$. Equivalently: $S_2(\Gamma_0(N))$ is spanned over $\mathbb{C}$ by cusp forms all of whose Fourier coefficients at the cusp $\infty$ are rational integers. No further hypothesis on $N$ is imposed, and the statement is about spanning only; it does not assert that $L$ is a lattice of full rank or free of the corresponding rank.
--
--   This is the weight-$2$ case of the classical integral structure (or $q$-expansion) statement for spaces of cusp forms on $\Gamma_0(N)$, reflecting the existence of a model of $X_0(N)$ over $\mathbb{Z}$ whose global differentials give the integral Fourier coefficients. It discharges the hypothesis [`CuspForm.HasIntegralStructure N 2`](def/CuspForm_IntegralStructure.html#L6) assumed elsewhere, and is used throughout the Hecke-algebra part of the development, for instance in the results on base change of the Hecke algebra and on eigenvectors in the torsion of cohomological carriers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_hasIntegralStructure_two.lean

import Mathlib
import Definitions.Def_CuspForm_IntegralStructure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.hasIntegralStructure_two (N : ℕ) [NeZero N] : CuspForm.HasIntegralStructure N 2 := by sorry
