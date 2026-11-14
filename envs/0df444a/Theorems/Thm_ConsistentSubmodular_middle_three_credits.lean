-- Prove2me | Theorems.Thm_ConsistentSubmodular_middle_three_credits
-- name    : ConsistentSubmodular.middle_three_credits
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:21:12.025264+00:00
-- url     : https://prove2.me/theorems/6ffd57eb-a350-4b83-9ffa-bdd24d9226f4
-- title:
--   Middle rollback — three scalar credit inequalities
-- statement:
--   Let $k,d_0,d,p,W,q,\delta,w,P$ be real numbers and put $c(k,d_0)=2-\frac{3}{k}+\frac{3(4-k)d_0}{k}$ (the quantity `middleCap`). Assume
--
--   - $\tfrac43\le k\le 2$, $d_0\ge 0$, $\tfrac{7}{40}\le d\le\tfrac14$, $d\le p\le 2d$;
--   - (parent) $p=(4-k)W-kd-(4-k)d_0$, $\;W+d_0\le p$, $\;kp\le 2k-3+3(4-k)d_0$;
--   - (child) $1\le q\le\tfrac43$, $\delta\ge 0$, $\;P=(4-q)w-q\delta-4d$, $\;p+w\le P$, $\;w\le 1-d-\delta$;
--   - (failed test) $0\le q\,(2-3d-P)-3(1-4d)$;
--   - (gain) $0\le k(4-k)\delta-p-(k-2)^2d+(4-k)(3-k)d_0$.
--
--   Then all three of the following hold:
--
--   1. $\;0< d-2\,c(k,d_0)+3p-(3-k)W$;
--   2. $\;0\le p+(3-2k)(d+\delta)-2(4-k)d_0$;
--   3. $\;0< P-(k-1)+(k-2)^2(d+\delta)-(4-k)^2d_0$.
--
--   The first and third inequalities are strict, the second is weak.
--
--   This is the purely scalar core of the middle-rollback case of the clairvoyant certificate construction: the parent row (with attained envelope value $p$) and the child row (with value $P$) together yield the three credits that later cover every row of the suffix.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/MiddleCredits.lean#L261-L290 (`ConsistentSubmodular.middle_three_credits`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_MiddleCredits

open ConsistentSubmodular

theorem ConsistentSubmodular.middle_three_credits (k d₀ d p W q δ w P : ℝ)
    (hk : (4 : ℝ) / 3 ≤ k) (hk2 : k ≤ 2) (hd₀ : 0 ≤ d₀)
    (hd7 : (7 : ℝ) / 40 ≤ d) (hd4 : d ≤ 1 / 4) (hpd : d ≤ p) (hp : p ≤ 2 * d)
    (hparentatt : p = (4 - k) * W - k * d - (4 - k) * d₀)
    (hparentper : W + d₀ ≤ p)
    (hparent : k * p ≤ 2 * k - 3 + 3 * (4 - k) * d₀)
    (hq1 : 1 ≤ q) (hq4 : q ≤ (4 : ℝ) / 3) (hδ : 0 ≤ δ)
    (hatt : P = (4 - q) * w - q * δ - 4 * d) (hper : p + w ≤ P)
    (hcap : w ≤ 1 - d - δ) (hfailed : 0 ≤ q * (2 - 3 * d - P) - 3 * (1 - 4 * d))
    (hG : 0 ≤ k * (4 - k) * δ - p - (k - 2) ^ 2 * d + (4 - k) * (3 - k) * d₀) :
    0 < d - 2 * middleCap k d₀ + 3 * p - (3 - k) * W ∧
    0 ≤ p + (3 - 2 * k) * (d + δ) - 2 * (4 - k) * d₀ ∧
    0 < P - (k - 1) + (k - 2) ^ 2 * (d + δ) - (4 - k) ^ 2 * d₀ := by sorry
