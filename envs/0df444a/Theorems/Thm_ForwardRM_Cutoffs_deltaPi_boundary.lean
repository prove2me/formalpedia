-- Prove2me | Theorems.Thm_ForwardRM_Cutoffs_deltaPi_boundary
-- name    : ForwardRM.Cutoffs.deltaPi_boundary
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T18:59:09.852983+00:00
-- url     : https://prove2.me/theorems/334338ab-1095-45d6-a0e0-dc3fc96ae304
-- title:
--   Footnote 12 — ΔΠ^k_t(v̲) ≤ m(v̲) < 0 and ΔΠ^k_t(v̄) = (1−δ)m(v̄) > 0 for t ≤ T − 1
-- statement:
--   Let $1\le t\le T-1$ and $k\ge 1$, and suppose (as in the proof of Theorem 1) that the future cutoffs $\{x^j_s\}_{s\ge t+1}$, $j\le k$, are deterministic and decreasing in $j$. Then, with no lower buyers,
--
--   $$
--   \Delta\Pi^k_t(\underline v)\le m(\underline v)<0,\qquad \Delta\Pi^k_t(\bar v)=(1-\delta)\,m(\bar v)>0 .
--   $$
--
--   These boundary values are what allow the intermediate value theorem to produce the cutoff $x^k_t$ in the proof of Theorem 1.
--
--   **Formalization Note** The statement is restricted to $t\le T-1$: in the last period $\Delta\Pi^k_T(y)=m(y)$, so the printed equality $\Delta\Pi^k_T(\bar v)=(1-\delta)m(\bar v)$ would be false there; the proof of Theorem 1 treats period $T$ separately ("$m(x^k_T)=0$"). The strict positivity uses the model's assumption $m(\bar v)>0$, which this footnote is the source of.
-- source:
--   Board, Skrzypacz, Revenue Management with Forward-Looking Buyers, J. Political Economy 124(4) (2016), accepted manuscript of Feb. 6, 2015, p. 16, footnote 12 (proof of Theorem 1)

import Mathlib
import Definitions.Def_ForwardRM_Cutoffs_Model
import Definitions.Def_ForwardRM_Cutoffs_ValueFunction
import Definitions.Def_ForwardRM_Cutoffs_Cutoff

namespace ForwardRM.Cutoffs

/-- Footnote 12 (Board–Skrzypacz, p. 16): in a period `t ≤ T − 1`, under the backward-induction
hypothesis of the proof of Theorem 1 (future cutoffs deterministic and decreasing in `j ≤ k`),
`ΔΠ^k_t(v̲) ≤ m(v̲) < 0` while `ΔΠ^k_t(v̄) = (1 − δ) m(v̄) > 0`. -/
theorem deltaPi_boundary (M : Model) (t k : ℕ) (ht : 1 ≤ t) (htT : t + 1 ≤ M.T) (hk : 1 ≤ k)
    (hH : M.FutureCutoffsDecreasing t k) :
    M.deltaPi t k M.vlo 0 ≤ M.m M.vlo ∧ M.m M.vlo < 0 ∧
      M.deltaPi t k M.vhi 0 = (1 - M.δ) * M.m M.vhi ∧ 0 < (1 - M.δ) * M.m M.vhi := by sorry

end ForwardRM.Cutoffs
