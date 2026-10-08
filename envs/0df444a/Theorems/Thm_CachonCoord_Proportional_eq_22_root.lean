-- Prove2me | Theorems.Thm_CachonCoord_Proportional_eq_22_root
-- name    : CachonCoord.Proportional.eq_22_root
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:44:18.574929+00:00
-- url     : https://prove2.me/theorems/f62b9090-24ca-4844-bee4-e26a0df09d51
-- title:
--   Eq. (22), p. 51 — L_n(q) increases from 0 to 1, so (22) has a unique root q* > 0 when b < w < p
-- statement:
--   For $n \ge 2$ let
--
--   $$
--   L_n(q) = \frac1n F(q) + \left(\frac{n-1}{n}\right)\left(\frac1q\int_0^q F(x)\,dx\right),
--   $$
--
--   the left-hand side of (22). Then
--
--   1. $L_n$ is strictly increasing on $(0,\infty)$;
--   2. $L_n(q) \to 0$ as $q \to 0^+$;
--   3. $L_n(q) \to 1$ as $q \to \infty$;
--   4. for every contract with $b < w < p$ there is exactly one $q^* > 0$ with $L_n(q^*) = \dfrac{p-w}{p-b}$.
--
--   The root $q^*$ is the equilibrium total order of the $n$ retailers.
--
--   **Formalization Note** The book's "from 0 (when $q^* = 0$) to 1 (when $q^* = \infty$)" is read as the two limits. The hypotheses on the demand law are the chapter's standing assumptions (p. 7), carried by the model.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.5.1, Eq. (22), p. 51 and the two sentences after it

import Mathlib
import Definitions.Def_CachonCoord_Proportional_Demand
import Definitions.Def_CachonCoord_Proportional_Nash
import Definitions.Def_CachonCoord_Proportional_Game

namespace CachonCoord.Proportional

open Filter Topology

/-- p. 51, Eq. (22): "The left hand side of (22) is increasing in `q*` from 0 (when `q* = 0`)
to 1 (when `q* = ∞`). Hence, when `b < w < p`, there exists a unique `q*` that satisfies (22)."
Here `L_n(q) = (1/n) F(q) + ((n − 1)/n) (1/q) ∫_0^q F` is strictly increasing on `q > 0`, tends to
`0` as `q → 0⁺` and to `1` as `q → ∞`, and `L_n(q*) = (p − w)/(p − b)` has exactly one root
`q* > 0`. -/
theorem eq_22_root (M : Model) (n : ℕ) (hn : 2 ≤ n) :
    StrictMonoOn (M.lhs22 n) (Set.Ioi 0) ∧
      Tendsto (M.lhs22 n) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (M.lhs22 n) atTop (𝓝 1) ∧
      ∀ w b : ℝ, b < w → w < M.p →
        ∃! qs : ℝ, 0 < qs ∧ M.lhs22 n qs = (M.p - w) / (M.p - b) := by sorry

end CachonCoord.Proportional
