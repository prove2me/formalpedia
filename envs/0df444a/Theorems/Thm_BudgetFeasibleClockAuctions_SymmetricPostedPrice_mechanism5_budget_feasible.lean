-- Prove2me | Theorems.Thm_BudgetFeasibleClockAuctions_SymmetricPostedPrice_mechanism5_budget_feasible
-- name    : BudgetFeasibleClockAuctions.SymmetricPostedPrice.mechanism5_budget_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:33:00.155851+00:00
-- url     : https://prove2.me/theorems/2cc262f1-dbb0-45a1-8ecd-7ec7447e0d38
-- title:
--   Theorem 15 proof — budget feasibility (corrected: payment endpoint and reserve)
-- statement:
--   Let $N$ have $n$ bidders, let the public budget be $B$, let $0\le c_i\le B$ be their real costs, and choose any reserve $j\in N$. Bidders are processed in any public order. Acceptance includes equality. Use Mechanism 5 with the proof-consistent fallback acquisition, and write $(W,p)$ for its final winning set and offered-price record. Only $p_i$ for $i\in W$ is paid. A chosen reserve entails $n\ge1$ and affordability entails $B\ge0$; singleton and zero-budget instances remain included.
--
--   For each prefix of $t\le n-1$ scanned bidders, let $W_t$ be its computed winners, let $p^t$ record offers made so far, and let $k_t$ be its acceptance count. Write $H_m=\sum_{h=1}^m1/h$, with $H_0=0$. Then
--
--   $$k_t=|W_t|\le t,\qquad
--   \sum_{i\in W_t}p_i^t=
--   \begin{cases}0&k_t=0,\\ B(1+H_{k_t-1})/(2\ln n)&k_t\ge1,\end{cases}
--   \qquad 0\le\sum_{i\in W_t}p_i^t\le B.$$
--
--   If $n\ge2$ and $B>0$, each prefix spends strictly less than $B$. The final output satisfies
--
--   $$\sum_{i\in W}p_i\le B.$$
--
--   If the complete scan count is zero, $W=\{j\}$ and the final payment is exactly $B$. At $n=1$ the only scan prefix is empty, so no logarithmic offer is executed. This statement supplies exact payment accounting and budget feasibility throughout the actual mechanism.
--
--   Differences from the source:
--   - correction: Mechanism 5 line 13 offers B to j but does not update W → insert j and pay its accepted fallback offer when the scan count is zero; reason: Case 1 explicitly returns j; n=4, B=1, all costs and marginals 1 give empty output under the literal code but OPT=1
--   - correction: opening payment display uses 1+1+1/2+...+1/(n-1) and concludes spending < B → k actual scan acceptances spend B(1+H_(k-1))/(2 ln n), zero when k=0; all prefixes and the final output spend at most B, with strict scan spending only when n≥2 and B>0; reason: n=3, B=1, zero costs and unit marginals give printed spending 1.137799>B but actual spending 0.910239; the fallback spends exactly B and B=0 gives equality
--   - encoding: an arbitrarily ordered nonempty finite bidder set and arbitrary reserve → Fin n in increasing label order, universally quantified costs and reserve j:Fin n; reason: every public order is represented by relabeling; j entails n≥1 and 0≤c_j≤B entails B≥0, without excluding n=1 or B=0
--   - encoding: pay the accepted offer to every winner → sum the published offered-price record only over computed winners; reason: the record also contains rejected offers; actual payment is that record on W and zero outside W
--   - encoding: at any time of execution the mechanism does not exhaust the budget → every prefix of length t≤n-1 is the published step folded over the first t nonreserve labels; its count equals its winner cardinality and is at most t; reason: these are the computed prefixes of the same scan, without an assumed run invariant or performance certificate
-- source:
--   Balkanski et al., Deterministic Budget-Feasible Clock Auctions, arXiv:2107.09239v2, §B.2, Theorem 15 proof, opening unnumbered payment display, printed p. 27, PDF p. 28; standing model §2, printed p. 5, PDF p. 6; symmetric valuation §B.2, printed p. 25, PDF p. 26

import Mathlib
import Definitions.Def_BudgetClock_PostedSym_Setting
import Theorems.Thm_BudgetClock_PostedSym_payment_bound

open BudgetClock.PostedSym

namespace BudgetFeasibleClockAuctions.SymmetricPostedPrice

/-- arXiv:2107.09239v2, Theorem 15 proof, opening display, printed p. 27 / PDF p. 28.
Corrected: k acceptances contribute 1 + H_(k-1), not 1 + H_(n-1).
The fallback inserts the accepting reserve as Case 1 requires. Singleton and zero budgets
are included; only the interior scan bound is strict. Prefixes use the published step. -/
theorem mechanism5_budget_feasible (n : ℕ) (B : ℝ) (c : Fin n → ℝ)
    (hc0 : ∀ i, 0 ≤ c i) (hcB : ∀ i, c i ≤ B) (j : Fin n) :
    (∀ t : ℕ, t ≤ n - 1 →
      let s : ScanState n :=
        (((List.finRange n).filter (fun i => i ≠ j)).take t).foldl (step n B c)
          { count := 0, winners := ∅, price := fun _ => 0 }
      s.count = s.winners.card ∧ s.count ≤ t ∧
      (∑ i ∈ s.winners, s.price i) =
        (if s.count = 0 then 0 else
          B * (1 + ∑ h ∈ Finset.range (s.count - 1), 1 / ((h : ℝ) + 1)) /
            (2 * Real.log n)) ∧
      0 ≤ (∑ i ∈ s.winners, s.price i) ∧
      (∑ i ∈ s.winners, s.price i) ≤ B ∧
      (2 ≤ n → 0 < B → (∑ i ∈ s.winners, s.price i) < B)) ∧
    (∑ i ∈ (mech5 n B c j).1, (mech5 n B c j).2 i) ≤ B ∧
    ((scan n B c j).count = 0 →
      (mech5 n B c j).1 = {j} ∧
      (∑ i ∈ (mech5 n B c j).1, (mech5 n B c j).2 i) = B) := by sorry

end BudgetFeasibleClockAuctions.SymmetricPostedPrice
