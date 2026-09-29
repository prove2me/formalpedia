-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isIrreducibleGL2RealKTypeModule_lower_eq_zero_iff_of_one_le
-- name    : AutomorphicForm.exists_isIrreducibleGL2RealKTypeModule_lower_eq_zero_iff_of_one_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/8126a06e-ec5d-5cfd-91a4-1534fb2eae3d
-- title:
--   Irreducible GL₂(ℝ) K-type module with lowest weight k
-- statement:
--   Let $k$ be an integer with $1 \le k$. The assertion is that there exist a complex vector space $M$ (a type carrying an additive commutative group structure and a $\mathbb{C}$-module structure), a family of $\mathbb{C}$-subspaces $\mathrm{wt}(n) \subseteq M$ indexed by $n \in \mathbb{Z}$, and three $\mathbb{C}$-linear endomorphisms $E, L, \varepsilon$ of $M$, with the following six properties. First, `IsGL2RealKTypeModule` holds for $(\mathrm{wt}, E, L, \varepsilon)$: the family $\mathrm{wt}$ is an internal direct sum decomposition of $M$; $E$ maps $\mathrm{wt}(n)$ into $\mathrm{wt}(n+2)$ and $L$ maps $\mathrm{wt}(n)$ into $\mathrm{wt}(n-2)$ for every $n$; for $v \in \mathrm{wt}(n)$ one has $E(Lv) - L(Ev) = n\,v$; $\varepsilon$ maps $\mathrm{wt}(n)$ into $\mathrm{wt}(-n)$, satisfies $\varepsilon \circ \varepsilon = \mathrm{id}$ and $\varepsilon \circ E = L \circ \varepsilon$. Second, each $\mathrm{wt}(n)$ is finite-dimensional over $\mathbb{C}$. Third, `IsIrreducibleGL2RealKTypeModule` holds: $M \neq 0$, and every subspace $W$ with $W \le \bigsqcup_n (W \sqcap \mathrm{wt}(n))$ (i.e. spanned by its weight components) and with $W$ stable under each of $E$, $L$, $\varepsilon$ is either $\bot$ or $\top$. Fourth, the set of $n$ with $\mathrm{wt}(n) \neq \bot$ is infinite. Fifth, $\mathrm{wt}(n) \neq \bot$ precisely when $k \le |n|$ and $n - k$ is even. Sixth, for every integer $k'$ there is a nonzero $v \in \mathrm{wt}(k')$ with $Lv = 0$ if and only if $k' = k$.
--
--   This is the existence, in the $\mathrm{SO}(2)$-type presentation used in the project, of the irreducible $(\mathfrak{g},K)$-module of $\mathrm{GL}_2(\mathbb{R})$ of lowest weight $k \ge 1$ — the discrete series for $k \ge 2$ and the limit of discrete series for $k = 1$ — characterised by its weights $|n| \ge k$, $n \equiv k \pmod 2$ and by the fact that the lowering operator annihilates a nonzero vector only in weight $k$. It supplies the archimedean input for [`AutomorphicForm.exists_isGL2RealKTypeModule_archOccursInClassOf_iff_isArchLoweringAnnihilatedAt_of_coversModCentre`](thm.html#AutomorphicForm.exists_isGL2RealKTypeModule_archOccursInClassOf_iff_isArchLoweringAnnihilatedAt_of_coversModCentre).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isIrreducibleGL2RealKTypeModule_lower_eq_zero_iff_of_one_le.lean

import Mathlib
import Definitions.Def_AutomorphicForm_GL2RealKTypeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AutomorphicForm

theorem AutomorphicForm.exists_isIrreducibleGL2RealKTypeModule_lower_eq_zero_iff_of_one_le
    (k : ℤ) (hk : 1 ≤ k) :
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module ℂ M) (wt : ℤ → Submodule ℂ M)
      (E L ε : M →ₗ[ℂ] M),
      IsGL2RealKTypeModule wt E L ε ∧ (∀ n : ℤ, FiniteDimensional ℂ (wt n)) ∧
      IsIrreducibleGL2RealKTypeModule wt E L ε ∧ {n : ℤ | wt n ≠ ⊥}.Infinite ∧
      (∀ n : ℤ, wt n ≠ ⊥ ↔ (k ≤ |n| ∧ Even (n - k))) ∧
      (∀ k' : ℤ, (∃ v ∈ wt k', v ≠ 0 ∧ L v = 0) ↔ k' = k) := by sorry
