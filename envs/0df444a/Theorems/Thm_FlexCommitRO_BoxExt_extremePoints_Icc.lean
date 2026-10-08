-- Prove2me | Theorems.Thm_FlexCommitRO_BoxExt_extremePoints_Icc
-- name    : FlexCommitRO.BoxExt.extremePoints_Icc
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T03:59:50.847383+00:00
-- url     : https://prove2.me/theorems/a7eedb8d-cad3-4d32-b45f-7d43e0c8f694
-- title:
--   Appendix, p. 269 — the extreme points of a segment [a, b] with a < b are a and b
-- statement:
--   Let $a < b$ be real numbers. The set of extreme points of the segment $[a,b] \subset \mathbb R$ is its pair of endpoints:
--   $$
--   \operatorname{ext}[a,b] = \{a, b\}.
--   $$
--
--   In the Appendix this identifies $\operatorname{ext}(\mathcal U_t) = \{d_t^{\min}, d_t^{\max}\}$, which is how the problem $(P_+)$ of Proposition 1 is written.
-- source:
--   Ben-Tal, Golany, Nemirovski & Vial, Retailer-supplier flexible commitments contracts: a robust optimization approach, MSOM 7(3) (2005), p. 269, Appendix, first paragraph (ext(𝒰_t) = {d_t^min, d_t^max})

import Mathlib

namespace FlexCommitRO.BoxExt

theorem extremePoints_Icc (a b : ℝ) (hab : a < b) :
    (Set.Icc a b).extremePoints ℝ = {a, b} := by sorry

end FlexCommitRO.BoxExt
