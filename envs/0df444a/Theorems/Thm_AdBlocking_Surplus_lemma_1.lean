-- Prove2me | Theorems.Thm_AdBlocking_Surplus_lemma_1
-- name    : AdBlocking.Surplus.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:43.801423+00:00
-- url     : https://prove2.me/theorems/38269042-861e-4313-8764-6241a1955f61
-- title:
--   Lemma 1 — optimal quality and advertising without an adblocker
-- statement:
--   For $p_a,c>0$, $0<r\le1$, and $0\le t\le1$, the benchmark publisher's optimal ad volume at each fixed $q>0$ is uniquely $A^*(q)$ from equation (2). Maximizing the resulting profit over $q\ge0$ gives the unique equilibrium quality $q^*_{NA}$ from Lemma 1:
--
--   $$q^*_{NA}=\begin{cases}p_a/[4c(1+r)(1-t)],&t\le r/(1+r),\\ p_a(1-r(1-t)+t)/(4c),&t>r/(1+r).\end{cases}$$
--
--   The equilibrium quality and ad volume are weakly decreasing in $r$ and $c$, and weakly increasing in $t$ and $p_a$. This benchmark supplies both the no-adblocker comparison and the ad choice used in the adblocker regime.
--
--   **Formalization Note** Comparative statics use weak order to include endpoint equalities. At $q=0$, the statement selects $A^*(0)=0$ and asserts equilibrium quality through that explicit selection.
-- source:
--   Gritckevich, Katona & Sarvary, Ad Blocking, SSRN 3100524 (version of March 7, 2021), p. 14 (PDF 15), equation (2) and Lemma 1; p. 40 (PDF 41), proof

import Mathlib
import Definitions.Def_AdBlocking_Surplus_Model
import Definitions.Def_AdBlocking_Surplus_ClosedForms

namespace AdBlocking.Surplus

theorem lemma_1 :
    ∀ pa c r t : ℝ, Standing pa c r t →
      (∀ q : ℝ, 0 < q → ∀ A : ℝ,
        IsBenchAdBest pa r t q A ↔ A = benchAdStar r t q) ∧
      (∀ q : ℝ, 0 ≤ q →
        (IsBenchEq pa c r t (benchAdStar r t) q ↔
          q = benchQualityStar pa c r t)) ∧
      (∀ r' : ℝ, r ≤ r' → r' ≤ 1 →
        benchQualityStar pa c r' t ≤ benchQualityStar pa c r t ∧
        benchEqAdStar pa c r' t ≤ benchEqAdStar pa c r t) ∧
      (∀ c' : ℝ, c ≤ c' →
        benchQualityStar pa c' r t ≤ benchQualityStar pa c r t ∧
        benchEqAdStar pa c' r t ≤ benchEqAdStar pa c r t) ∧
      (∀ t' : ℝ, t ≤ t' → t' ≤ 1 →
        benchQualityStar pa c r t ≤ benchQualityStar pa c r t' ∧
        benchEqAdStar pa c r t ≤ benchEqAdStar pa c r t') ∧
      (∀ pa' : ℝ, pa ≤ pa' →
        benchQualityStar pa c r t ≤ benchQualityStar pa' c r t ∧
        benchEqAdStar pa c r t ≤ benchEqAdStar pa' c r t) := by sorry

end AdBlocking.Surplus
