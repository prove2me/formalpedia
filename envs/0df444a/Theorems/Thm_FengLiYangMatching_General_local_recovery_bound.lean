-- Prove2me | Theorems.Thm_FengLiYangMatching_General_local_recovery_bound
-- name    : FengLiYangMatching.General.local_recovery_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T20:30:05.322876+00:00
-- url     : https://prove2.me/theorems/144a92bc-9975-4b34-b1c1-119934beabb0
-- title:
--   Finite local recovery inequality
-- statement:
--   Let $B$ be a finite simple graph whose vertices avoid two distinct new vertices $x_1,x_2$. Let $Y$ avoid these two vertices, and let the potential edges join $\{x_1,x_2\}$ to $Y$. Mark a set of $k\le2$ vertices of $Y$, each having a potential edge to a distinct one of $x_1,x_2$.
--
--   Choose one uniform order of all base and potential edges, and independently retain each potential edge with probability $q\in[5/8,1]$. Run Greedy on the base edges and on the base together with retained potential edges, sharing this order. Let $N$ count the new vertices matched in the augmented run, $R$ the marked vertices matched there, and $K$ the marked vertices matched in the base run. Then
--
--   $$
--   \mathbb E[3N+2R+K]\ge3k.
--   $$
--
--   This finite local inequality is the recovery comparison in Equation (10), including its zero-, one-, and two-reference cases.
-- source:
--   Feng, Li, Yang, Improved Bounds for Online Matching with Random Edge Arrivals, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1018.pdf, Section 4.1, p. 13, equivalent formulation of the coupled matchings and Equation (10); Sections 4.2–4.3, pp. 14–16.

import Definitions.Def_FengLiYangMatching_General_Local
open MeasureTheory Finset

namespace FengLiYangMatching.General
theorem local_recovery_bound {n : ℕ} (d : Local n) (hd : d.Valid) (hpartners : d.Partners)
    (q : ℝ) (hq : 5/8 ≤ q) (hq1 : q ≤ 1) :
    localMean d q (fun σ r => 3*N d σ r+2*R d σ r+K d σ) ≥ 3*d.marked.card := by sorry

end FengLiYangMatching.General
