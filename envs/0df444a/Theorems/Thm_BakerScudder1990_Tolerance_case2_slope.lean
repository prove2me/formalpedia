-- Prove2me | Theorems.Thm_BakerScudder1990_Tolerance_case2_slope
-- name    : BakerScudder1990.Tolerance.case2_slope
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T06:10:29.608287+00:00
-- url     : https://prove2.me/theorems/62a26528-47f5-489e-aa48-29cc07c2d34d
-- title:
--   Appendix, proof of Property III(G), Case 2 — slope of $f$ inside a tolerance window
-- statement:
--   Consider an instance of the single-machine common-due-date model with tolerances, with jobs in a fixed sequence and completion times $C_1 < \dots < C_n$. Fix a job $j$ and suppose the due date $d$ and the larger due date $d+\varepsilon$, $\varepsilon > 0$, both lie strictly inside the tolerance window of job $j$,
--
--   $$
--   C_j - v_j < d < d + \varepsilon < C_j + u_j .
--   $$
--
--   Then job $j$ incurs no penalty, the jobs $i < j$ are early, the jobs $i > j$ are tardy, and
--
--   $$
--   f(d+\varepsilon) - f(d) = \Bigl[\sum_{i<j} \alpha_i - \sum_{i>j} \beta_i\Bigr]\varepsilon .
--   $$
--
--   This is Case 2 of the paper's proof of Property III(G). When $u_j = v_j = 0$ the window is a single point and the statement is empty, as in the paper.
--
--   **Formalization Note** The paper prints $\Delta f(\varepsilon) = f(S) - f(S') = [\sum_{i\in B,\, i\ne j}\alpha_i - \sum_{i\in A,\, i\ne j}\beta_i]\varepsilon$, with the opposite sign; the stated identity is the correct one, $f(S') - f(S)$. Positions are 0-based ($k = j - 1$); the sums run over positions $i < k$ and $i > k$.
-- source:
--   Baker and Scudder, Sequencing with earliness and tardiness penalties: a review, Oper. Res. 38 (1990), p. 34, Appendix, proof of Property III(G), Case 2 (sign of Δf corrected)

import Mathlib
import Definitions.Def_BakerScudder1990_Tolerance_Instance

namespace BakerScudder1990.Tolerance

open Instance

/-- Appendix, proof of Property III(G), Case 2 (Baker and Scudder 1990, p. 34), with the sign
corrected: when the due date lies strictly inside the tolerance window of job `k`,
`(C_k - v_k, C_k + u_k)`, raising it by `ε > 0` inside that window changes the total penalty by
`(∑_{i<k} α_i - ∑_{i>k} β_i) ε` (job `k` pays nothing). The paper prints
`f(S) - f(S') = [∑_{B, i≠j} α - ∑_{A, i≠j} β] ε`; the correct identity is `f(S') - f(S)`.
Positions are 0-based. -/
theorem case2_slope {n : ℕ} (I : Instance n) (k : Fin n) (d ε : ℝ) (hε : 0 < ε)
    (hlo : I.C k - I.v k < d) (hhi : d + ε < I.C k + I.u k) :
    I.cost (d + ε) - I.cost d =
      ((∑ i ∈ Finset.univ.filter (fun i : Fin n => i < k), I.α i) -
        (∑ i ∈ Finset.univ.filter (fun i : Fin n => k < i), I.β i)) * ε := by sorry

end BakerScudder1990.Tolerance
