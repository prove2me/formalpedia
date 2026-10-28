-- Prove2me | Theorems.Thm_D1Bound5_forbidden_interval_chain
-- name    : D1Bound5.forbidden_interval_chain
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:30:06.951604+00:00
-- url     : https://prove2.me/theorems/9bf00421-ea2c-4942-96cc-51890fcc3aa3
-- title:
--   Forbidden interval chain
-- statement:
--   The logical interval-chain step used in Section common-intervals. All endpoints are closed. The input intervals need not have distinct ends.
-- source:
--   D1Bound5/IntervalChain.lean, lines 5-21, SHA-256 d7dd36dcbdb75d91109bf3d72af86d3dd5262d911be4745485984f19b92291c4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Order.Archimedean.Real.Basic

section
namespace D1Bound5


theorem _root_.D1Bound5.forbidden_interval_chain {R : Type*} [LinearOrder R]
    (lower upper : ℕ → R) (x : R)
    (hstart : lower 0 ≤ x)
    (hoverlap : ∀ n, lower (n+1) ≤ upper n)
    (hexcluded : ∀ n, ¬ (lower n ≤ x ∧ x ≤ upper n))
    (hunbounded : ∃ n, x < lower n) : False := by sorry







end D1Bound5
end
