-- Prove2me | Theorems.Thm_BakerScudder1990_Tolerance_case1_slope
-- name    : BakerScudder1990.Tolerance.case1_slope
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T06:10:21.996657+00:00
-- url     : https://prove2.me/theorems/d29ed133-824b-4a31-8fce-30610a260b7c
-- title:
--   Appendix, proof of Property III(G), Case 1 — slope of $f$ between two tolerance windows
-- statement:
--   Consider an instance of the single-machine common-due-date model with tolerances, with jobs in a fixed sequence and completion times $C_1 < \dots < C_n$. Fix a position $j \in \{1,\dots,n+1\}$ and suppose the due date $d$ and the larger due date $d+\varepsilon$, $\varepsilon > 0$, both lie in the open gap between the window of job $j-1$ and the window of job $j$,
--
--   $$
--   C_{j-1} + u_{j-1} < d < d + \varepsilon < C_j - v_j ,
--   $$
--
--   where the lower bound is absent for $j = 1$ and the upper bound is absent for $j = n+1$. Then the jobs $B = \{i < j\}$ are early, the jobs $A = \{i \ge j\}$ are tardy, and
--
--   $$
--   f(d+\varepsilon) - f(d) = \Bigl[\sum_{i<j} \alpha_i - \sum_{i \ge j} \beta_i\Bigr]\varepsilon .
--   $$
--
--   So $f$ is affine on each such gap, with slope $-\sum_i \beta_i$ before the first window and $\sum_i \alpha_i$ after the last one. This is Case 1 of the paper's proof of Property III(G); together with Case 2 it shows that $f$ is piecewise linear with breakpoints at the window ends $C_j - v_j$ and $C_j + u_j$.
--
--   **Formalization Note** The paper prints the identity as $\Delta f(\varepsilon) = f(S) - f(S') = [\sum_{B}\alpha_i - \sum_{A}\beta_i]\varepsilon$, i.e. with the opposite sign; raising $d$ makes every early job earlier (cost $+\alpha_i\varepsilon$) and every tardy job less late (cost $-\beta_i\varepsilon$), so the correct identity is $f(S') - f(S) = [\dots]\varepsilon$, which is what is stated. Positions are 0-based: the gap index is $k = j-1 \in \{0,\dots,n\}$ (`Fin (n+1)`), the lower bound is imposed through the job $i$ with $i + 1 = k$ (none when $k = 0$) and the upper bound through the job $i = k$ (none when $k = n$); the sums run over positions $i < k$ and $i \ge k$.
-- source:
--   Baker and Scudder, Sequencing with earliness and tardiness penalties: a review, Oper. Res. 38 (1990), p. 34, Appendix, proof of Property III(G), Case 1 (sign of Δf corrected)

import Mathlib
import Definitions.Def_BakerScudder1990_Tolerance_Instance

namespace BakerScudder1990.Tolerance

open Instance

/-- Appendix, proof of Property III(G), Case 1 (Baker and Scudder 1990, p. 34), with the sign
corrected: when the due date lies strictly between the end of the window of the job just before
position `k` (`C_i + u_i` for the position `i` with `i + 1 = k`) and the start of the window of job `k` (`C_k - v_k`), raising it by
`ε > 0` inside that gap changes the total penalty by `(∑_{i<k} α_i - ∑_{i≥k} β_i) ε`. The paper
prints `f(S) - f(S') = [∑_B α - ∑_A β] ε`; the correct identity is `f(S') - f(S)`.
Here `k : Fin (n + 1)` is 0-based; `k = 0` is the gap before the first window (no lower bound)
and `k = n` is the gap after the last window (no upper bound). -/
theorem case1_slope {n : ℕ} (I : Instance n) (k : Fin (n + 1)) (d ε : ℝ) (hε : 0 < ε)
    (hlo : ∀ i : Fin n, i.val + 1 = k.val → I.C i + I.u i < d)
    (hhi : ∀ i : Fin n, i.val = k.val → d + ε < I.C i - I.v i) :
    I.cost (d + ε) - I.cost d =
      ((∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k.val), I.α i) -
        (∑ i ∈ Finset.univ.filter (fun i : Fin n => k.val ≤ i.val), I.β i)) * ε := by sorry

end BakerScudder1990.Tolerance
