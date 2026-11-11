-- Prove2me | Theorems.Thm_CapacitatedKMedianFPT_Main_fact_1
-- name    : CapacitatedKMedianFPT.Main.fact_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T07:13:26.455532+00:00
-- url     : https://prove2.me/theorems/87296e18-b8b1-488b-a71b-2fad8711cfaa
-- title:
--   Fact 1 — (log m)^t ≤ m · t!
-- statement:
--   For every integer $t\ge0$ and every $m\ge1$,
--   $$(\log m)^t\le m\cdot t!,$$
--   where $\log$ is the natural logarithm.
--
--   This bound turns enumeration counts such as $(\log n/\varepsilon)^{t}$ with $t$ depending on $k$ only into FPT bounds $n\cdot g(k,\varepsilon)$.
--
--   Differences from the source:
--
--   - generalization: m ≥ 1 (applied to integers) → every real m ≥ 1; reason: the statement does not restrict m to integers; integers m ≥ 1 are a special case
--   - reading: log → natural logarithm Real.log; reason: the proof expands m = e^{log m}
-- source:
--   Aditya Anand, Yichen Huang, Ragesh Jaiswal, Amit Kumar, Euiwoong Lee, Jatin Yadav, A Tight FPT Approximation for Capacitated k-Median, STOC 2027 submission #1646 (October 2026), p. 6, Fact 1; proof p. 22–23

import Mathlib

set_option autoImplicit false

namespace CapacitatedKMedianFPT.Main

/-- **Fact 1** (p. 6, proof p. 22–23). `(log m)^t ≤ m · t!` for all integers `t ≥ 0` and all real
`m ≥ 1` (natural logarithm). -/
theorem fact_1 (t : ℕ) (m : ℝ) (hm : 1 ≤ m) :
    Real.log m ^ t ≤ m * (t.factorial : ℝ) := by sorry

end CapacitatedKMedianFPT.Main
