-- Prove2me | Theorems.Thm_ConsistentSubmodular_relayError_nonpos_of_baseline
-- name    : ConsistentSubmodular.relayError_nonpos_of_baseline
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:20:06.425075+00:00
-- url     : https://prove2.me/theorems/990720c0-3e2f-472c-aa88-4c52449666bd
-- title:
--   Relay error is nonpositive for a baseline in the admissible range
-- statement:
--   Let $A,D,b,w$ be real numbers with $0\le D\le w\le A$ and $D\le b\le 2A-w$. Define the relay error
--   $$\operatorname{err}(A,D,b,w)=b^2-b\,(2A+2w-D)+D\,(A+w).$$
--   Then
--
--   $$\operatorname{err}(A,D,b,w)\;\le\;0.$$
--
--   The relay error is a quadratic in $b$ that is nonpositive on the whole baseline range $[D,\,2A-w]$. The statement is a scalar inequality used to certify the relay step of the certificate construction.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/RelayError.lean#L34-L47 (`ConsistentSubmodular.relayError_nonpos_of_baseline`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_RelayError

open ConsistentSubmodular

theorem ConsistentSubmodular.relayError_nonpos_of_baseline (A D b w : ℝ)
    (hD : 0 ≤ D) (hDw : D ≤ w) (hwA : w ≤ A)
    (hDb : D ≤ b) (hb : b ≤ 2 * A - w) : relayError A D b w ≤ 0 := by sorry
