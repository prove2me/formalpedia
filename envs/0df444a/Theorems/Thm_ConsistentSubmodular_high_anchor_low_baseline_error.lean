-- Prove2me | Theorems.Thm_ConsistentSubmodular_high_anchor_low_baseline_error
-- name    : ConsistentSubmodular.high_anchor_low_baseline_error
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:19:55.146231+00:00
-- url     : https://prove2.me/theorems/9ff4d64a-24b3-41e8-94bc-70adc2b1de60
-- title:
--   Nonpositive relay error at high anchors with low baseline
-- statement:
--   Let $E(A,D,b,w)=b^2-b\,(2A+2w-D)+D\,(A+w)$ be the relay error. Let $d,p\in\mathbb{R}$ satisfy $0\le d\le\tfrac{7}{40}$, $p\ge 0$, $p\le 2d$, and $d\le p(1-p)$. Then
--   $$E\bigl(1-d,\;3d,\;p+d,\;3d\bigr)\;\le\;0 .$$
--
--   This covers the low-baseline corner of the high-anchor regime in the relay-error analysis of the safe-path certificates (Appendix B), complementing the case treated in the large-parameter relay-error bound.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/HighAnchor.lean#L85-L103 (`ConsistentSubmodular.high_anchor_low_baseline_error`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_RelayError

open ConsistentSubmodular

theorem ConsistentSubmodular.high_anchor_low_baseline_error (d p : ℝ)
    (hd : 0 ≤ d) (hd7 : d ≤ 7 / 40) (hp : 0 ≤ p) (hp2d : p ≤ 2 * d)
    (hcredit : d ≤ p * (1 - p)) :
    relayError (1 - d) (3 * d) (p + d) (3 * d) ≤ 0 := by sorry
