-- Prove2me | Theorems.Thm_AdInterm_SPE_anticipated_report_law
-- name    : AdInterm.SPE.anticipated_report_law
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:18.867658+00:00
-- url     : https://prove2.me/theorems/a684eb6c-b579-4739-827a-c5edb3638a53
-- title:
--   §3.3, p. 19 (after Def. 3.3) — under the ψ-mechanisms each tier-t report has the law of the anticipated report W_t, siblings' reports independent
-- statement:
--   Consider the symmetric $k$-tree ($k_t\ge1$ for $t=1,\dots,n+1$) with i.i.d. buyer values of law $V$ (a buyer law with strictly increasing virtual value), and suppose Assumption 3.1 holds for $W_1,\dots,W_n$. Let every intermediary in tier $t=1,\dots,n$ use the mechanism $(z_{W_{t-1}},\psi_{W_{t-1}})$, and count a node that sends no report as reporting $0$.
--
--   1. For every tier $t\le n$ and every node $j$ of tier $t$, the report of $I_{(t,j)}$ has the law of the anticipated report:
--   $$
--   \operatorname{Law}\big(\text{report of }I_{(t,j)}\big)=W_t .
--   $$
--   2. For every node of tier $t+1$ ($t\le n$; the seller included), the reports of its $k_{t+1}$ children are mutually independent.
--
--   This is the sentence "the anticipated report $W_t$ coincides with the report of an intermediary in tier $t$ to the upstream mechanism if all intermediaries use the projected virtual value functions". It is what lets each tier optimize against i.i.d. copies of $W_{t-1}$ in Theorem 3.1.
--
--   **Formalization Note** "Reports zero" below the reserve is no report in the game; here it is read back as $0$, the page's convention. Laws are pushforwards of the product law of the buyers' values.
-- source:
--   Balseiro, Candogan & Gurkan, Multi-stage Intermediation in Display Advertising, SSRN 2661459 (manuscript of 2019-08-17; M&SOM doi:10.1287/msom.2019.0854), §3.3, paragraph after Definition 3.3, p. 19

import Mathlib
import Definitions.Def_AdInterm_SPE_Setting

open MeasureTheory ProbabilityTheory

namespace AdInterm.SPE

theorem anticipated_report_law (n : ℕ) (k : ℕ → ℕ)
    (hk : ∀ t, 1 ≤ t → t ≤ n + 1 → 1 ≤ k t)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hV : BuyerLaw μ) (hVinc : IncVV μ)
    (hA : ∀ t, 1 ≤ t → t ≤ n →
      RegularPos (annLaw k μ t) ∧ IncVV (annLaw k μ t)) :
    (∀ t, t ≤ n → ∀ j, j < nodes k n t →
      (Measure.pi (fun _ : Fin (nodes k n 0) => μ)).map
          (fun v => (bid k (fun s _ => eqMech k μ s) (buyerValues k n v) t j).unbotD 0) =
        annLaw k μ t) ∧
      (∀ t, t ≤ n → ∀ p, p < nodes k n (t + 1) →
        iIndepFun
          (fun (c : Fin (k (t + 1))) (v : Fin (nodes k n 0) → ℝ) =>
            (bid k (fun s _ => eqMech k μ s) (buyerValues k n v) t
              (p * k (t + 1) + c)).unbotD 0)
          (Measure.pi (fun _ : Fin (nodes k n 0) => μ))) := by sorry

end AdInterm.SPE
