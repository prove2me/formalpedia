-- Prove2me | Theorems.Thm_BIInsurance_Screening_proposition_1_i
-- name    : BIInsurance.Screening.proposition_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:40.762015+00:00
-- url     : https://prove2.me/theorems/571f8bfd-6eb1-4994-81cc-a13973630c11
-- title:
--   Proposition 1(i), p. 14 — the optimal effort e∗(s) is non-increasing and concave in s on [0, s̄], and e∗(s) ≤ ê
-- statement:
--   Assume the standing assumptions and let $m\ge\mu_L+\delta_L$. On the coverage interval $[0,\bar s]$ the firm's optimal recovery effort with insurance $e^*(s)$ of (4.13) satisfies:
--   1. $s\mapsto e^*(s)$ is non-increasing;
--   2. $s\mapsto e^*(s)$ is concave;
--   3. $e^*(s)\le\hat e$ for every $s\in[0,\bar s]$, where $\hat e$ is the optimal effort without insurance (4.7).
--
--   $$
--   e^*(s)\ \text{non-increasing and concave on }[0,\bar s],\qquad e^*(s)\le\hat e .
--   $$
--
--   Insurance and recovery effort are substitutes: more coverage lowers the effort, at an increasing rate.
--
--   **Formalization Note** The page's "for all $s$" is read as $s\in[0,\bar s]$, the coverage set; beyond the cap on $\bar s$ the logarithm in (4.14) can have a non-positive argument. The statement holds for every location $m\ge\mu_L+\delta_L$, which contains the four values $\mu_i+\delta_j$.
-- source:
--   Kao, Keskin & Shang, Impact of information asymmetry and limited production capacity on business interruption insurance, SSRN 3184530 (version of May 13, 2020), p. 14, Proposition 1(i); proof p. 32

import Mathlib
import Definitions.Def_BIInsurance_Screening_Model

namespace BIInsurance.Screening

theorem proposition_1_i (P : Params) (hS : P.Standing) (m : ℝ) (hm : P.muL + P.dL ≤ m) :
    AntitoneOn (eStar P m) (Set.Icc 0 P.sbar) ∧
      ConcaveOn ℝ (Set.Icc 0 P.sbar) (eStar P m) ∧
      ∀ s ∈ Set.Icc 0 P.sbar, eStar P m s ≤ eHat P m := by sorry

end BIInsurance.Screening
