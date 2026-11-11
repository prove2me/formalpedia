-- Prove2me | Theorems.Thm_EliasGlobalClock_LowerBound_binary_entropy_bounds
-- name    : EliasGlobalClock.LowerBound.binary_entropy_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T07:03:23.067532+00:00
-- url     : https://prove2.me/theorems/28090595-e4c9-41d4-abb7-a4dc41c1a6da
-- title:
--   Fact D.3 — both binary entropy bounds, with endpoints
-- statement:
--   For $0\le x\le1$, let $h(x)=-x\ln x-(1-x)\ln(1-x)$, with $h(0)=h(1)=0$. Then both inequalities hold:
--
--   $$h(x)\le 2\ln\bigl(\sqrt x+\sqrt{1-x}\bigr)\le2\sqrt{x(1-x)}.$$
--
--   All logarithms are natural and both constants are exactly $2$. The statement includes both endpoints. These estimates relate a coordinate's binary entropy to the contention weight in Lemma 4.2.
--
--   Differences from the source:
--   - encoding: the binary entropy h with h(0)=h(1)=0 → Mathlib Real.binEntropy on the closed unit interval; reason: its natural-log and zero-mass conventions agree exactly with the source
-- source:
--   Kuowen Chen, Shengquan Du, Tsvi Kopelowitz, Seth Pettie, Ben Plosk, STOC 2027 submission #1311 (October 2026), printed p.36, PDF p.37, Fact D.3 (proof continues on printed p.37, PDF p.38); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1311.pdf

import Mathlib

namespace EliasGlobalClock.LowerBound

/-- Fact D.3, printed p.36 / PDF p.37, including x=0 and x=1. -/
theorem binary_entropy_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.binEntropy x ≤ 2 * Real.log (Real.sqrt x + Real.sqrt (1 - x)) ∧
    2 * Real.log (Real.sqrt x + Real.sqrt (1 - x)) ≤
      2 * Real.sqrt (x * (1 - x)) := by sorry

end EliasGlobalClock.LowerBound
