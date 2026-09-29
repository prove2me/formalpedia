-- Prove2me | Theorems.Thm_AutomorphicForm_exists_kernel_concentrating_translatesSpanFinite_maximalCompactAt
-- name    : AutomorphicForm.exists_kernel_concentrating_translatesSpanFinite_maximalCompactAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/22f7fe75-c889-5f2a-8907-193922e31501
-- title:
--   K-finite approximate identity on the archimedean maximal compact subgroup
-- statement:
--   Let $K$ be a number field. Write $\mathcal{K} =$ `maximalCompactAt K ∅` for the subgroup of $\mathrm{GL}_2(\mathbb{A}_K)$ consisting of those $k$ whose finite part lies in `finiteIntegralGL2` and whose archimedean component at each infinite place $w$ satisfies `IsRowIsometry`, intersected — because the finite set of places is empty, so its complement is everything — with the kernels of all the maps $k \mapsto$ (image of the finite part of $k$ in $\mathrm{GL}_2(K_v)$), $v$ running over all height-one primes of $\mathcal{O}_K$; thus the finite part of $k$ is trivial and the archimedean parts are row isometries. Equip $\mathcal{K}$ with the Haar measure `maximalCompactAtHaar K ∅`, the Haar measure associated with the whole group, and with the Borel $\sigma$-algebra coming from the Borel structure on adelic $\mathrm{GL}_2$. The assertion is the existence of a sequence $\kappa : \mathbb{N} \to \mathcal{K} \to \mathbb{R}$ such that: every $\kappa_n$ is continuous; $\kappa_n(k) \ge 0$ for all $n,k$; $\int_{\mathcal{K}} \kappa_n \, dk = 1$ for all $n$; for every neighbourhood $U$ of $1$ in $\mathcal{K}$, $\int_{U^{c}} \kappa_n \, dk \to 0$ as $n \to \infty$; and for each $n$ there is a single finite set $s$ of real-valued functions on $\mathcal{K}$ such that every left translate $k \mapsto \kappa_n(ak)$, $a \in \mathcal{K}$, lies in the $\mathbb{R}$-span of $s$.
--
--   This provides an approximate identity at $1$ on the archimedean maximal compact subgroup of adelic $\mathrm{GL}_2$ whose members are translation-finite, i.e. the left translates of each kernel span a finite-dimensional space of functions; such kernels smooth a vector while keeping it inside a finite-dimensional space of $\mathcal{K}$-translates, with no appeal to Peter–Weyl. It is used in the proof of [`AutomorphicForm.exists_isArchKFinite_tendsto_and_setLIntegral_le_of_mem_isotypicCuspSubmodule`](thm.html#AutomorphicForm.exists_isArchKFinite_tendsto_and_setLIntegral_le_of_mem_isotypicCuspSubmodule), where elements of an isotypic cuspidal submodule are approximated by archimedean-finite vectors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_kernel_concentrating_translatesSpanFinite_maximalCompactAt.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.exists_kernel_concentrating_translatesSpanFinite_maximalCompactAt
    (K : Type) [Field K] [NumberField K] :
    ∃ κ : ℕ → ↥(maximalCompactAt K ∅) → ℝ,
      (∀ n, Continuous (κ n)) ∧ (∀ n k, 0 ≤ κ n k) ∧ (∀ n, ∫ k, κ n k ∂(maximalCompactAtHaar K ∅) = 1) ∧
      (∀ U ∈ nhds (1 : ↥(maximalCompactAt K ∅)),
        Filter.Tendsto (fun n => ∫ k in Uᶜ, κ n k ∂(maximalCompactAtHaar K ∅)) Filter.atTop (nhds 0)) ∧
      (∀ n, ∃ s : Finset (↥(maximalCompactAt K ∅) → ℝ), ∀ a : ↥(maximalCompactAt K ∅),
        (fun k => κ n (a * k)) ∈ Submodule.span ℝ (s : Set (↥(maximalCompactAt K ∅) → ℝ))) := by sorry
