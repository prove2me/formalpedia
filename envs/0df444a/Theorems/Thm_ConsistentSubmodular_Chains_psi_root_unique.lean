-- Prove2me | Theorems.Thm_ConsistentSubmodular_Chains_psi_root_unique
-- name    : ConsistentSubmodular.Chains.psi_root_unique
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:43.379126+00:00
-- url     : https://prove2.me/theorems/74576e6e-72b1-4c39-8ee9-af1d432e0a32
-- title:
--   Proposition 1 (uniqueness) — $\Psi$ has at most one root in $(1/2,1)$
-- statement:
--   Let $\Psi(\xi)=89\xi^4-44\xi^3-19\xi^2-3\xi+1$. If $\xi_1,\xi_2\in(1/2,1)$ satisfy $\Psi(\xi_1)=\Psi(\xi_2)=0$, then $\xi_1=\xi_2$.
--
--   This is the uniqueness part of Proposition 1: the root $\xi^\star\approx0.7942$ of $\Psi$ in $(1/2,1)$ is unique, so that $\xi^\star$ (defined as the supremum of such roots) is well defined. The argument rests on the strict convexity of $\Psi$ on $(1/2,1)$ together with $\Psi(1/2)<0$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/Constants.lean#L63-L89 (`ConsistentSubmodular.Chains.psi_root_unique`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open scoped BigOperators
open ConsistentSubmodular

theorem ConsistentSubmodular.Chains.psi_root_unique {ξ₁ ξ₂ : ℝ} (h₁ : 1 / 2 < ξ₁) (h₁' : ξ₁ < 1) (h₂ : 1 / 2 < ξ₂)
    (h₂' : ξ₂ < 1) (hψ₁ : psi ξ₁ = 0) (hψ₂ : psi ξ₂ = 0) : ξ₁ = ξ₂ := by sorry
