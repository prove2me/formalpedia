-- Prove2me | Theorems.Thm_FairRentFPTAS_Approx_lemma_8
-- name    : FairRentFPTAS.Approx.lemma_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:51.172803+00:00
-- url     : https://prove2.me/theorems/a5d1f71e-ff6d-401c-8167-daefd391697a
-- title:
--   Lemma 8, p. 17 — the rounded utilities are admissible and every slope is an integer power of (1+ε)
-- statement:
--   Let $\mathcal I$ be well formed and $0<\varepsilon<1$. The rounded utilities $\{\bar v_a(r,\cdot)\}_{a,r}$ are piecewise linear, continuous and strictly decreasing (well-formed: first break point $0$, increasing break points, positive slopes), and every slope is $(1+\varepsilon)^k$ for some integer $k$.
--
--   This is what allows Theorem 1 to be applied to $\bar{\mathcal I}$.
-- source:
--   Arunachaleswaran, Barman & Rathi, Fully Polynomial-Time Approximation Schemes for Fair Rent Division, arXiv:1807.04163v1, p. 17, Lemma 8

import Mathlib
import Definitions.Def_FairRentFPTAS_Approx_Model

namespace FairRentFPTAS.Approx

/-- Lemma 8, p. 17: the rounded utilities are well-formed continuous, strictly decreasing
piecewise-linear functions, and every slope is an integer power of `(1+ε)`. -/
theorem lemma_8 {n : ℕ} (I : Instance n) (ε : ℝ) (hI : Standing I) (hε : 0 < ε) (hε1 : ε < 1) :
    Standing (roundInst ε I) ∧ PowersProp ε (roundInst ε I) := by sorry

end FairRentFPTAS.Approx
