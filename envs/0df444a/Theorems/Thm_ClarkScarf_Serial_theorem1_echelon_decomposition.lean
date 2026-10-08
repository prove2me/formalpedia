-- Prove2me | Theorems.Thm_ClarkScarf_Serial_theorem1_echelon_decomposition
-- name    : ClarkScarf.Serial.theorem1_echelon_decomposition
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:28:35.13749+00:00
-- url     : https://prove2.me/theorems/cb16acee-3eb8-4341-9051-5eb3bb58fb04
-- title:
--   Theorem 1 (p. 482) — Cₙ(x₁, w₁, x₂) = Ĉₙ(x₁, w₁) + gₙ(x₂), and installation 1 follows its isolated policy
-- statement:
--   Consider the two-installation serial system of Clark and Scarf: installation 2 ships to installation 1 with a two-period lead time at unit cost $c_1\ge0$, system orders of size $z$ cost $c(z)=K+cz$ ($z>0$), $c(0)=0$, and arrive after one period, installation 1 pays the expected holding and shortage cost $L(x_1)$ of (1), echelon 2 pays a natural cost $\tilde L(x_2)$, demand has density $\varphi$ on $(0,\infty)$, and costs are discounted by $\alpha\ge0$. Let $C_n(x_1,w_1,x_2)$ be the optimal $n$-period system cost (14) and $\hat C_n(x_1,w_1)$ the optimal $n$-period cost of installation 1 in isolation (15), where $x_1$ is the stock on hand at installation 1, $w_1$ the stock in transit to it, and $x_2\ge x_1+w_1$ the echelon-2 stock.
--
--   1. **Decomposition (16).** There is a sequence of functions $g_n$ of echelon stock, with $g_1=\tilde L$, such that for every $n\ge1$ and every state with $x_1+w_1\le x_2$,
--   $$C_n(x_1,w_1,x_2)=\hat C_n(x_1,w_1)+g_n(x_2).$$
--   2. **Installation 1 provisions as in isolation.** Let $n+1$ periods remain and let $\hat y\ge x_1+w_1$ be an optimal target for the isolated problem (15), i.e. a minimizer of the expression in braces of (15). Then shipping up to $\min(x_2,\hat y)$, "getting as much as it can", is optimal in the system problem (14): for every system order $z\ge0$ and every feasible target $x_1+w_1\le y\le x_2$, the expression in braces of (14) at $(\min(x_2,\hat y),z)$ is at most its value at $(y,z)$.
--
--   Theorem 1 reduces the two-installation problem to two one-dimensional problems: installation 1 solves its own problem, and echelon 2 solves an inventory problem in $x_2$ alone with cost $\tilde L+\Lambda$.
--
--   **Formalization Note** The functions $g_n$ are quantified before every state variable, so they cannot depend on $(x_1,w_1)$. Part 2 is conditional on an isolated minimizer $\hat y$, exactly as the sentence it formalizes, and compares with the same $z$ on both sides, so it needs neither attainment of the infimum over $z$ nor the existence of critical numbers. The Lean index $n$ of the objective functions `isoObj`, `sysObj` refers to the problem with $n+1$ periods remaining. Added hypotheses (fields of the model): finite mean of the demand; $\tilde L$ non-negative, continuous and of linear growth; the sign conditions $h,p,\alpha,c_1,K,c\ge0$.
-- source:
--   Clark and Scarf, Optimal Policies for a Multi-Echelon Inventory Problem, Management Sci. 6(4), 1960, p. 482, Theorem 1, eq. (16)

import Mathlib
import Definitions.Def_ClarkScarf_Serial_Model

open MeasureTheory Set

namespace ClarkScarf.Serial

/-- Theorem 1, p. 482. (A) There is a sequence of functions `g_n(x₂)` with `g_1 = L̃` such that
`C_n(x₁, w₁, x₂) = Ĉ_n(x₁, w₁) + g_n(x₂)` (16) for every `n ≥ 1` and every state with
`x₁ + w₁ ≤ x₂`. (B) It is optimal for installation 1 to use an optimal target `ŷ` of its isolated
problem (15), truncated at the stock available, `min(x₂, ŷ)`. -/
theorem theorem1_echelon_decomposition (M : Model) :
    (∃ g : ℕ → ℝ → ℝ, (∀ x₂ : ℝ, g 1 x₂ = M.Lt x₂) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ x₁ w₁ x₂ : ℝ, x₁ + w₁ ≤ x₂ →
        M.sysCost n x₁ w₁ x₂ = M.isoCost n x₁ w₁ + g n x₂) ∧
    (∀ (n : ℕ) (x₁ w₁ x₂ yiso : ℝ), x₁ + w₁ ≤ x₂ → x₁ + w₁ ≤ yiso →
      (∀ y : ℝ, x₁ + w₁ ≤ y → M.isoObj n x₁ w₁ yiso ≤ M.isoObj n x₁ w₁ y) →
      ∀ y z : ℝ, x₁ + w₁ ≤ y → y ≤ x₂ → 0 ≤ z →
        M.sysObj n x₁ w₁ x₂ (min x₂ yiso) z ≤ M.sysObj n x₁ w₁ x₂ y z) := by sorry

end ClarkScarf.Serial
