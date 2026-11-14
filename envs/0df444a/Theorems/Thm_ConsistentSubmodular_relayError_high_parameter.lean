-- Prove2me | Theorems.Thm_ConsistentSubmodular_relayError_high_parameter
-- name    : ConsistentSubmodular.relayError_high_parameter
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:19:38.184462+00:00
-- url     : https://prove2.me/theorems/e9c367c8-ba35-45fc-82e7-82dee6648208
-- title:
--   Nonpositive relay error for high parameter and strong credit
-- statement:
--   Define the relay error $E(A,D,b,w)=b^2-b\,(2A+2w-D)+D\,(A+w)$. Let $d,p,b,w\in\mathbb{R}$ satisfy
--
--   * $0\le d<\tfrac14$ and $p\ge 0$;
--   * (strong credit) $\tfrac12\le p$ or $d\le p(1-p)$;
--   * $3d\le w\le 1-d$;
--   * $p+d\le b\le 2(1-d)-w$;
--   * $\tfrac{2}{3}\,\bigl((p+d)+3d\bigr)\le w$.
--
--   Then
--   $$E(1-d,\,3d,\,b,\,w)\;\le\;0 .$$
--
--   This scalar inequality is part of the relay analysis for safe polygonal paths in Appendix B: it shows that, on the large-parameter source domain, the strong-credit hypothesis makes the error term nonpositive.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/RelayError.lean#L94-L119 (`ConsistentSubmodular.relayError_high_parameter`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_RelayError

open ConsistentSubmodular

theorem ConsistentSubmodular.relayError_high_parameter (d p b w : ℝ)
    (hd : 0 ≤ d) (hd4 : d < 1 / 4) (hp : 0 ≤ p)
    (hcredit : (1 : ℝ) / 2 ≤ p ∨ d ≤ p * (1 - p))
    (hDw : 3 * d ≤ w) (hwA : w ≤ 1 - d)
    (hbL : p + d ≤ b) (hb : b ≤ 2 * (1 - d) - w)
    (hw : 2 * ((p + d) + 3 * d) / 3 ≤ w) :
    relayError (1 - d) (3 * d) b w ≤ 0 := by sorry
