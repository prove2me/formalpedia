-- Prove2me | Theorems.Thm_ConsistentSubmodular_high_relay_cubic_nonpositive
-- name    : ConsistentSubmodular.high_relay_cubic_nonpositive
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:19:23.484972+00:00
-- url     : https://prove2.me/theorems/fc0c844e-1537-4066-9391-f3e369e7af87
-- title:
--   Bernstein cubic certificate for the large-parameter relay
-- statement:
--   For every real $p$ with $0\le p\le\tfrac12$,
--
--   $$17p^3-41p^2+20p-3\;\le\;0.$$
--
--   This is the explicit Bernstein-type certificate for the cubic polynomial that arises in the large-parameter relay of the certificate construction; it is a pure one-variable polynomial inequality.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/RelayError.lean#L49-L76 (`ConsistentSubmodular.high_relay_cubic_nonpositive`)

import Mathlib

theorem ConsistentSubmodular.high_relay_cubic_nonpositive (p : ℝ) (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2) :
    17 * p ^ 3 - 41 * p ^ 2 + 20 * p - 3 ≤ 0 := by sorry
