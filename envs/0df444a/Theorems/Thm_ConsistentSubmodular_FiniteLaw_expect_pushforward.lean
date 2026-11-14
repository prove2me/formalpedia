-- Prove2me | Theorems.Thm_ConsistentSubmodular_FiniteLaw_expect_pushforward
-- name    : ConsistentSubmodular.FiniteLaw.expect_pushforward
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:21:21.371769+00:00
-- url     : https://prove2.me/theorems/75c5df7d-0b50-476c-882e-c6d70ad3caf0
-- title:
--   Expectation of a function of a finite-valued map (pushforward formula)
-- statement:
--   Let $\mu$ be a probability law on a finite set $\Omega$, let $\beta$ be a finite set, let $F:\Omega\to\beta$ and $v:\beta\to\mathbb R$. Then
--   $$\mathbb E_{\omega\sim\mu}\bigl[v(F(\omega))\bigr]\;=\;\sum_{b\in\beta}\mu\bigl(F=b\bigr)\,v(b),$$
--   where $\mu(F=b)=\sum_{\omega:\,F(\omega)=b}\mu(\omega)$.
--
--   This is the change-of-variables identity for the law of $F$, used to compute expectations of functions of a random object by summing over its values.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/FiniteProductLaw.lean#L25-L38 (`ConsistentSubmodular.FiniteLaw.expect_pushforward`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_FiniteProbability

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.FiniteLaw
variable {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)

theorem ConsistentSubmodular.FiniteLaw.expect_pushforward {β : Type*} [Fintype β] (F : Ω → β) (v : β → ℝ) :
    μ.expect (fun ω => v (F ω)) =
      ∑ b, μ.probability (fun ω => F ω = b) * v b := by sorry
