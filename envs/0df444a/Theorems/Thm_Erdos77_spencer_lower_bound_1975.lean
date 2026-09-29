-- Prove2me | Theorems.Thm_Erdos77_spencer_lower_bound_1975
-- name    : Erdos77.spencer_lower_bound_1975
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T18:22:54.11311+00:00
-- url     : https://prove2.me/theorems/1c568c68-83e6-4416-a750-3da64454040a
-- title:
--   Spencer 1975: $R(k) \ge (1+o(1))\frac{\sqrt2}{e}\,k\,2^{k/2}$
-- statement:
--   For every $\varepsilon>0$ there is $k_0$ such that for all $k\ge k_0$,
--
--   $$
--   R(k)\ \ge\ (1-\varepsilon)\,\frac{\sqrt2}{e}\,k\,2^{k/2}.
--   $$
--
--   Equivalently, $R(k)\ge(1+o(1))\frac{\sqrt2}{e}\,k\,2^{k/2}$ as $k\to\infty$. This is Spencer's 1975 improvement (via the Lovász Local Lemma) of Erdős's lower bound by a factor of $2$; it remains the best known lower bound up to lower-order terms, and it does not change the exponential base $\sqrt2$.
-- source:
--   J. Spencer, Ramsey's theorem — a new lower bound, J. Combin. Theory Ser. A 18 (1975), 108–115, https://doi.org/10.1016/0097-3165(75)90071-0 (main result: R(k) ≥ (1+o(1)) (√2/e) k 2^{k/2}).

import Mathlib
import Definitions.Def_Erdos77_diagonal_ramsey
open Filter Topology

namespace Erdos77
theorem spencer_lower_bound_1975 (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      (1 - ε) * (Real.sqrt 2 / Real.exp 1) * (k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2) ≤
        (diagonalRamsey k : ℝ) := by sorry
end Erdos77
