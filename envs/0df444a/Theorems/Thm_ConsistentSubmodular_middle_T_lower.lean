-- Prove2me | Theorems.Thm_ConsistentSubmodular_middle_T_lower
-- name    : ConsistentSubmodular.middle_T_lower
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:20:57.404939+00:00
-- url     : https://prove2.me/theorems/59aabe77-01af-4066-a266-731b4b8bfc4c
-- title:
--   Positivity of the middle quantity $T$ for $k\in[\tfrac43,\tfrac74]$
-- statement:
--   Define, for real $k,d_0,d,p$,
--   $$I(k,d_0,d,p)=(3-k)\,p-k\,d-2(4-k)\,d_0,$$
--   $$T(k,d_0,d,p)=\big(13-(k-2)^2\big)p+\big(16+5(k-2)^2\big)d-(4-k)(27-k-2k^2)\,d_0-2k(4-k)(k-1).$$
--   Let $k,d_0,d,p$ be real numbers with
--   $$\tfrac43\le k\le \tfrac74,\qquad d_0\ge 0,\qquad d\ge \tfrac7{40},\qquad p\le 2d,\qquad I(k,d_0,d,p)\ge 0.$$
--   Then
--   $$T(k,d_0,d,p)>0 .$$
--
--   This is the lower-range case ($k\le 7/4$) of the positivity of the middle credit expression $T$ in the middle-parent analysis of the deterministic certificate construction; it combines the one-variable sign facts for the polynomial coefficients with the linear constraints on $(d_0,d,p)$.
--
--   **Formalization Note.** `middleI` and `middleT` denote the expressions $I$ and $T$ above.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/MiddleCredits.lean#L97-L150 (`ConsistentSubmodular.middle_T_lower`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_MiddleCredits

open ConsistentSubmodular

theorem ConsistentSubmodular.middle_T_lower (k d₀ d p : ℝ)
    (hk : (4 : ℝ) / 3 ≤ k) (hk7 : k ≤ (7 : ℝ) / 4) (hd₀ : 0 ≤ d₀)
    (hd : (7 : ℝ) / 40 ≤ d) (hp : p ≤ 2 * d) (hI : 0 ≤ middleI k d₀ d p) :
    0 < middleT k d₀ d p := by sorry
