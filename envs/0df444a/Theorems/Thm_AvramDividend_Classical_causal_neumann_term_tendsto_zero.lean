-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_neumann_term_tendsto_zero
-- name    : AvramDividend.Classical.causal_neumann_term_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T22:14:39.605003+00:00
-- url     : https://prove2.me/theorems/f172e565-7b12-42bb-94e0-d51f6eabc324
-- title:
--   Summable causal Neumann corrections vanish under a unit index shift
-- statement:
--   For every time, pointwise summable Gaussian Neumann corrections tend to zero even when the sequence is shifted by one step. This is the remainder hypothesis for the dominated-convergence resolvent identity.
-- source:
--   Summability of every pointwise Neumann correction family implies that its (n+1)-st term tends to zero. This supplies the exact hQ limit hypothesis of causal_neumann_resolvent_dominated_convergence, complementing the Proved finite-sum limit and term-integrability lemmas.

import Mathlib.Data.Real.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
open Filter

theorem AvramDividend.Classical.causal_neumann_term_tendsto_zero
    (Q : ℕ → ℝ → ℝ)
    (hQ : ∀ x : ℝ, Summable (fun n : ℕ => Q n x)) :
    ∀ x : ℝ, Tendsto (fun n : ℕ => Q (n + 1) x)
      atTop (nhds (0 : ℝ)) := by sorry
