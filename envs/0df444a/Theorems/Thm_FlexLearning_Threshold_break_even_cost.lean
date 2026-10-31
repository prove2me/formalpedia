-- Prove2me | Theorems.Thm_FlexLearning_Threshold_break_even_cost
-- name    : FlexLearning.Threshold.break_even_cost
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:56.388907+00:00
-- url     : https://prove2.me/theorems/dfdb35cc-fd55-42c3-9b21-c7be2f02cb18
-- title:
--   §2.1, p. 8, Eq. (8) — the pooling benefits decrease in c_F and a unique break-even cost c̃_F ∈ [c, p) exists
-- statement:
--   In the static model with independent demands uniform on $[x, x+U]$ ($x \ge 0$, $U > 0$), price $p$ and dedicated unit cost $c$ with $0 \le c < p$, let the risk pooling benefits of flexibility be
--   $$\mathscr P(c_F) = \bar\pi_F(c_F) - \bar\pi_N, \qquad \text{Eq. (7)}.$$
--   Then:
--   1. $\mathscr P$ is strictly decreasing in $c_F$ on $[0, p]$;
--   2. there is exactly one $\tilde c_F \in [c, p)$ with $\mathscr P(\tilde c_F) = 0$, i.e. $\bar\pi_F(\tilde c_F) = \bar\pi_N$ (Eq. (8)).
--
--   This defines the break-even unit cost of flexibility at which Proposition 1 compares the two systems, and shows that the comparison is not vacuous.
--
--   **Formalization Note** The paper says "monotonically decreasing"; the strict version is stated, which uniqueness needs. The interval is half-open because at $c = 0$ the break-even cost is $c_F = 0 = c$.
-- source:
--   Chod, Markakis & Trichakis, On the Learning Benefits of Resource Flexibility, SSRN preprint 3212177 (version of December 6, 2019), p. 8 (PDF 8), §2.1, Eqs. (7)–(8)

import Mathlib
import Definitions.Def_FlexLearning_Threshold_Model

namespace FlexLearning.Threshold

theorem break_even_cost (p c x U : ℝ) (hc : 0 ≤ c) (hcp : c < p) (hx : 0 ≤ x) (hU : 0 < U) :
    StrictAntiOn (fun cF : ℝ => piBarF p x U cF - piBarN p c x U) (Set.Icc 0 p) ∧
    ∃! cF : ℝ, cF ∈ Set.Ico c p ∧ IsBreakEven p c x U cF := by sorry

end FlexLearning.Threshold
