-- Prove2me | Theorems.Thm_CuspForm_HasNebentypus_sum_filter_eq_of_sum_eq
-- name    : CuspForm.HasNebentypus.sum_filter_eq_of_sum_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/6164dfb7-0ab9-57ab-9f11-8be8a86bda01
-- title:
--   Nebentypus components of a sum of cusp forms
-- statement:
--   Fix a positive integer $N$ and an integer $k$, and let $\iota$ be a type, $s \subseteq \iota$ a finite subset, $\chi : \iota \to$ (Dirichlet characters modulo $N$ with values in $\mathbb{C}$) a family of such characters, and $g : \iota \to$ (cusp forms of weight $k$ for $\Gamma_1(N)$) a family of cusp forms. Assume that for every $i \in s$ the form $g_i$ has nebentypus $\chi_i$, in the sense of [`CuspForm.HasNebentypus`](def/CuspForm_PrimitiveFormGamma1.html#L13): for all $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lying in $\Gamma_0(N)$ and all $\tau$ in the upper half-plane, $g_i(\gamma \cdot \tau) = \chi_i(d \bmod N)\,(c\tau + d)^k\, g_i(\tau)$, where $c = \gamma_{10}$ and $d = \gamma_{11}$. Assume further that a cusp form $f$ of weight $k$ for $\Gamma_1(N)$ has nebentypus $\varepsilon$ in the same sense, and that $\sum_{i \in s} g_i = f$. The conclusion is that the partial sum over the indices with prescribed character already equals $f$: $$\sum_{i \in s,\ \chi_i = \varepsilon} g_i = f,$$ equivalently the summands with $\chi_i \neq \varepsilon$ add up to $0$.
--
--   This is the linear independence of the nebentypus subspaces $S_k(N,\chi) \subseteq S_k(\Gamma_1(N))$ for distinct Dirichlet characters $\chi$ modulo $N$, in the form of a cancellation statement for a finite sum; combined with the decomposition of an arbitrary cusp form into diamond eigencomponents it gives $S_k(\Gamma_1(N)) = \bigoplus_\chi S_k(N,\chi)$. It is used in the project when extracting the nebentypus-$\varepsilon$ part of a cusp form written as a sum, notably in [`CuspForm.exists_qCoeff_eq_sum_isPrimitiveForm_of_hasNebentypus`](thm.html#CuspForm.exists_qCoeff_eq_sum_isPrimitiveForm_of_hasNebentypus) and in the analysis of Hecke eigenforms with prescribed $q$-expansion coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_HasNebentypus_sum_filter_eq_of_sum_eq.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.HasNebentypus.sum_filter_eq_of_sum_eq
    {N : ℕ} [NeZero N] {k : ℤ} [DecidableEq (DirichletCharacter ℂ N)] {ι : Type*} (s : Finset ι)
    (χ : ι → DirichletCharacter ℂ N) (g : ι → CuspForm (Gamma1 N) k)
    (hg : ∀ i ∈ s, CuspForm.HasNebentypus (χ i) (g i))
    {ε : DirichletCharacter ℂ N} {f : CuspForm (Gamma1 N) k} (hf : CuspForm.HasNebentypus ε f)
    (hsum : ∑ i ∈ s, g i = f) :
    ∑ i ∈ s.filter (fun i => χ i = ε), g i = f := by sorry
