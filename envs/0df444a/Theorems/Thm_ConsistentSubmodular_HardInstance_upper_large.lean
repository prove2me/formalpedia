-- Prove2me | Theorems.Thm_ConsistentSubmodular_HardInstance_upper_large
-- name    : ConsistentSubmodular.HardInstance.upper_large
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:24:49.671194+00:00
-- url     : https://prove2.me/theorems/66d3e2d4-4c44-4692-aedf-25ef3da47d5e
-- title:
--   Randomized upper bound is trivial for $\rho\ge1$
-- statement:
--   Let $k>0$, $\varepsilon\in\mathbb R$ and $\rho\ge1$. Then there exist a stream length $n$, a universe $\{0,\dots,u-1\}$ and sets $\mathrm{cover}(e)\subseteq\{0,\dots,u-1\}$ for the stream elements $e\in\{0,\dots,n-1\}$ such that the following holds. For every randomized algorithm $\mu$ all of whose realizations are feasible with cardinality budget $k$ and change budget $\lfloor\varepsilon k\rfloor$, there are a time $t\in\{0,\dots,n\}$ and a set $A\subseteq X_t$ with $|A|\le k$ such that $f(A)>0$ and
--   $$\mathbb E_\mu\bigl[f(\mathrm{ALG}_t)\bigr]\le\rho\,f(A),$$
--   where $f(B)=\bigl|\bigcup_{e\in B}\mathrm{cover}(e)\bigr|$ is the unweighted coverage.
--
--   For $\rho\ge1$ the bound holds trivially: one element covers the whole universe. It handles the range of $\rho$ not covered by the main argument of Theorem 1 (Appendix A.2).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/Impossibility/HardInstance.lean#L285-L309 (`ConsistentSubmodular.HardInstance.upper_large`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open scoped BigOperators
open Finset
open ConsistentSubmodular

theorem ConsistentSubmodular.HardInstance.upper_large {k : ℕ} {ε ρ : ℝ} (hk : 0 < k) (hρ : 1 ≤ ρ) :
    ∃ (n u : ℕ) (cover : Fin n → Finset (Fin u)),
      ∀ μ : RandomTrajectory n, μ.Feasible k ⌊ε * k⌋₊ →
        ∃ (t : Fin (n + 1)) (A : Finset (Fin n)),
          A ⊆ arrivedPrefix n t.val ∧ A.card ≤ k ∧ 0 < coverageValue cover A ∧
          μ.expectation (coverageValue cover) t ≤ ρ * coverageValue cover A := by sorry
