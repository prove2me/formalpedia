-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_normal_domain_sssp_adapter
-- name    : DecrAlmostLinearSSSP.Decremental.normal_domain_sssp_adapter
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T10:40:05.575666+00:00
-- url     : https://prove2.me/theorems/30ec9b8b-815d-4737-835f-5cafff296743
-- title:
--   General-weight adapter above the exact-recomputation threshold
-- statement:
--   Assume one fixed deterministic scalar RAM program maintains approximate source distances on valid inputs with at least two vertices, weights bounded by the square of the size bound, and accuracy strictly between $1/m$ and $1$. Suppose its total charged maintenance work is at most $Cma(m)/\epsilon$, where $C>0$ and $a$ is positive and subpolynomial.
--
--   Then a fixed deterministic scalar RAM adapter maintains the full distance array for every valid input with $n\ge2$, arbitrary integer weight bound $W\ge1$, and $1/m<\epsilon\le1$. For a positive constant $D$ and positive subpolynomial function $b$, its charged work satisfies
--
--   $$
--   \operatorname{work}\le Dmb(m)\epsilon^{-1}\max(1,\log_2 W).
--   $$
--
--   The adapter terminates after initialization and every legal deletion prefix, maintains simultaneous multiplicative accuracy and exact unreachability, and answers a stored-array query in nine charged instructions. The program and bounds are uniform over all input parameters and streams. This isolates the general-weight reduction needed to extend the polynomial-weight theorem to the full domain.
-- source:
--   Cui, Li, Miao and Wang, Partially Dynamic Single-Source Shortest Paths in Almost-Linear Time, October 2026 submission #912, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/912.pdf, p.4, unnumbered arbitrary-weight scaling reduction; finite scalar RAM implementation and explicit adapter constants formalize this reduction.

import Mathlib
import Definitions.Def_DecrAlmostLinearSSSP_Decremental_Adapters
set_option autoImplicit false
open scoped ENNReal NNReal
open DecrAlmostLinearSSSP.Decremental

theorem DecrAlmostLinearSSSP.Decremental.normal_domain_sssp_adapter
    (p : Program) (C : ℝ) (a : ℕ → ℝ) (queryBound : ℕ)
    (hC : 0 < C) (ha : Subpolynomial a)
    (hpoly : ∀ x : Input, x.Valid → 2 ≤ x.n → x.W ≤ x.size^2 →
      1/(x.size : ℝ) < x.accuracy → x.accuracy < 1 → Maintains p C a queryBound false x) :
    ∃ (host : Program) (D : ℝ) (b : ℕ → ℝ), 0 < D ∧ Subpolynomial b ∧
      ∀ i : Input, i.Valid → 2 ≤ i.n → 1/(i.size : ℝ) < i.accuracy → Maintains host D b 9 true i := by sorry
