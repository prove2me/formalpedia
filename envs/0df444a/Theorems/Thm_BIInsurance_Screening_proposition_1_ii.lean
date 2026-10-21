-- Prove2me | Theorems.Thm_BIInsurance_Screening_proposition_1_ii
-- name    : BIInsurance.Screening.proposition_1_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:35.213278+00:00
-- url     : https://prove2.me/theorems/143550d2-05c5-42ed-8968-d67449bd44a8
-- title:
--   Proposition 1(ii), p. 14 — the firm's expected profit with BI insurance is non-decreasing and convex in the coverage s
-- statement:
--   Assume the standing assumptions, let $\mu\ge\mu_L$ be an early demand forecast and $y\in\mathbb R$ a premium. Then the firm's expected profit with the BI insurance $(y,s)$,
--
--   $$
--   s\longmapsto E_{\delta,Z}\big[\pi^I_i(K,y,s)\big],
--   $$
--
--   defined by (4.16) with the optimal effort $e^*(s)$ under disruption, is non-decreasing and convex on the coverage interval $[0,\bar s]$.
--
--   Higher coverage is always (weakly) more valuable to the firm, and increasingly so; this is why the insurer can extract premiums for positive coverage.
--
--   **Formalization Note** The page states the result for $\mu=\mu_i$, $i\in\{H,L\}$; here every $\mu\ge\mu_L$ is allowed.
-- source:
--   Kao, Keskin & Shang, Impact of information asymmetry and limited production capacity on business interruption insurance, SSRN 3184530 (version of May 13, 2020), p. 14, Proposition 1(ii); proof pp. 32–33

import Mathlib
import Definitions.Def_BIInsurance_Screening_Model

namespace BIInsurance.Screening

theorem proposition_1_ii (P : Params) (hS : P.Standing) (mu y : ℝ) (hmu : P.muL ≤ mu) :
    MonotoneOn (fun s => EpiI P mu y s) (Set.Icc 0 P.sbar) ∧
      ConvexOn ℝ (Set.Icc 0 P.sbar) (fun s => EpiI P mu y s) := by sorry

end BIInsurance.Screening
