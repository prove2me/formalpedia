-- Prove2me | Theorems.Thm_FlagshipMEA_Monopoly_eq_C9
-- name    : FlagshipMEA.Monopoly.eq_C9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:08:41.577786+00:00
-- url     : https://prove2.me/theorems/394231f3-a2eb-4dea-b508-d6bffb16b1c8
-- title:
--   Equation (C–9) — revenue as a weighted ratio of MEA-index components
-- statement:
--   For a feasible marketing allocation $m$ with positive total effort $M=\sum_i m_i$, let $A_i(M)$ and $B_i(M)$ be the numerator and denominator of product $i$'s MEA index. Equation (C–9) rewrites the firm's revenue as
--
--   $$\operatorname{rev}(m)=\frac{\sum_i m_i A_i(M)}{\sum_i m_i B_i(M)}.$$
--
--   This identity puts the fixed-effort revenue objective in the form needed by Lemma 3. **Formalization Note** The condition $M>0$ is needed because $A_i$ and $B_i$ contain $1/M$.
-- source:
--   He, Ke & Zhang, A Model of Product Line Marketing, SSRN 3631879 (version of August 2021), p. 41 (PDF 43), proof of Lemma 4, equation (C–9)

import Mathlib
import Definitions.Def_FlagshipMEA_Monopoly_Model

namespace FlagshipMEA.Monopoly

/-- The last line of (C–9), p. 41, for a nonzero feasible TME. -/
theorem eq_C9 {n : ℕ} (D : Data n) (hS : D.Standing)
    (m : Fin n → ℝ) (hm : Feasible m) (hM : 0 < tme m) :
    D.revenue m =
      (∑ i, m i * D.A i (tme m)) / (∑ i, m i * D.B i (tme m)) := by sorry

end FlagshipMEA.Monopoly
