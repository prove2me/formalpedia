-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isIrreducibleGL2RealKTypeModule_ne_bot_iff_even_sub
-- name    : AutomorphicForm.exists_isIrreducibleGL2RealKTypeModule_ne_bot_iff_even_sub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/47e3b8d3-7ffd-5a74-afbd-a156b242bbd7
-- title:
--   Existence of irreducible K-type modules of each parity
-- statement:
--   For every integer $e$ there exist a type $M$ carrying the structure of an abelian group and of a complex vector space, a family of complex subspaces $\mathrm{wt}(n) \subseteq M$ indexed by $n \in \mathbb{Z}$, and three $\mathbb{C}$-linear endomorphisms $E, L, \varepsilon$ of $M$, with the following properties. First, the data $(\mathrm{wt}, E, L, \varepsilon)$ satisfy `IsGL2RealKTypeModule`: the family $\mathrm{wt}$ is an internal direct sum decomposition of $M$; $E$ maps $\mathrm{wt}(n)$ into $\mathrm{wt}(n+2)$ and $L$ maps $\mathrm{wt}(n)$ into $\mathrm{wt}(n-2)$; for $v \in \mathrm{wt}(n)$ one has $E(Lv) - L(Ev) = n \cdot v$; $\varepsilon$ maps $\mathrm{wt}(n)$ into $\mathrm{wt}(-n)$, satisfies $\varepsilon \circ \varepsilon = \mathrm{id}$, and satisfies $\varepsilon \circ E = L \circ \varepsilon$. Second, every $\mathrm{wt}(n)$ is finite-dimensional over $\mathbb{C}$. Third, the data are irreducible in the sense of `IsIrreducibleGL2RealKTypeModule`: $M$ contains a nonzero vector, and every subspace $W \subseteq M$ with $W \le \bigsqcup_{n} (W \sqcap \mathrm{wt}(n))$ and $W$ stable under $E$, $L$ and $\varepsilon$ is either $\bot$ or $\top$. Fourth, the set of $n$ with $\mathrm{wt}(n) \neq \bot$ is infinite. Fifth, $\mathrm{wt}(n) \neq \bot$ holds exactly when $n - e$ is even. Sixth, $L$ is injective on each weight space: if $v \in \mathrm{wt}(k)$ and $Lv = 0$ then $v = 0$.
--
--   This is the existence of the infinite-dimensional irreducible principal series $(\mathfrak{g}, K)$-modules of $\mathrm{GL}_2(\mathbb{R})$ of either parity, presented through their $\mathrm{SO}(2)$-types, the last clause recording the absence of a lowest weight vector. It is used in the comparison, at the archimedean place, between occurrence in a given class and annihilation by the lowering operator.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isIrreducibleGL2RealKTypeModule_ne_bot_iff_even_sub.lean

import Mathlib
import Definitions.Def_AutomorphicForm_GL2RealKTypeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AutomorphicForm

theorem AutomorphicForm.exists_isIrreducibleGL2RealKTypeModule_ne_bot_iff_even_sub (e : ℤ) :
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module ℂ M) (wt : ℤ → Submodule ℂ M)
      (E L ε : M →ₗ[ℂ] M),
      IsGL2RealKTypeModule wt E L ε ∧ (∀ n : ℤ, FiniteDimensional ℂ (wt n)) ∧
      IsIrreducibleGL2RealKTypeModule wt E L ε ∧ {n : ℤ | wt n ≠ ⊥}.Infinite ∧
      (∀ n : ℤ, wt n ≠ ⊥ ↔ Even (n - e)) ∧
      (∀ (k : ℤ) (v : M), v ∈ wt k → L v = 0 → v = 0) := by sorry
