-- Prove2me | Theorems.Thm_BSS_floor_halting_time_lower_bound
-- name    : BSS.floor_halting_time_lower_bound
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-14T15:07:49.325124+00:00
-- url     : https://prove2.me/theorems/e0cbdd6c-ddfd-42cc-844f-326a28b86976
-- title:
--   §4 Prop. 3: computing $\lfloor x \rfloor$ costs at least $\log_2 x$ infinitely often
-- statement:
--   Proposition 3 of §4 (p. 22). Suppose a machine $M$ over $\mathbb{R}$ computes the greatest integer
--   function on the positive reals. Then $T_M(x) \ge \log_2 x$ for an unbounded set of $x$.
--
--   The paper's argument is topological: for each nonnegative integer $l$ there is an open set of
--   inputs on which the machine outputs $l$; the time-$T$ halting set is covered by at most $2^{T}$
--   pieces $V_\gamma$ on each of which $\varphi_M$ is a rational map, hence constant when its values
--   are integers; so at least $L$ pieces are needed to realize the values below $L$, giving
--   $2^{T_L} \ge L$.
-- source:
--   L. Blum, M. Shub, S. Smale, On a theory of computation and complexity over the real numbers: NP-completeness, recursive functions and universal machines, Bull. Amer. Math. Soc. (N.S.) 21 (1989), no. 1, 1-46, https://doi.org/10.1090/S0273-0979-1989-15750-9, §4, p. 22, Proposition 3

import Definitions.Def_BSSFeasibility

namespace BSS

theorem floor_halting_time_lower_bound (M : Machine ℝ)
    (hM : ∀ x : ℝ, 0 < x → M.Halts (Finsupp.single 0 x) ∧
      M.outputVal (Finsupp.single 0 x) = (⌊x⌋ : ℝ)) :
    ∀ L : ℝ, ∃ x : ℝ, L < x ∧
      Real.logb 2 x ≤ (M.haltingTime (Finsupp.single 0 x) : ℝ) := by sorry

end BSS
