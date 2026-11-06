-- Prove2me | Theorems.Thm_BianchiIX_summable_probability_weighted
-- name    : BianchiIX.summable_probability_weighted
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T19:07:44.622688+00:00
-- url     : https://prove2.me/theorems/32539a9a-dadb-4983-812e-0fee4e793682
-- title:
--   Summability of bounded observables against a probability mass
-- statement:
--   Let $p:I\to\mathbb R$ be nonnegative with convergent sum one.
--   If $f:I\to\mathbb R$ satisfies $|f_i|\leq M$ for every $i$, then
--   the family $(p_if_i)_{i\in I}$ is summable.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/DiscreteMass.lean#L47-L53

import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace BianchiIX
end BianchiIX

open Filter
open scoped Topology
open BianchiIX

theorem BianchiIX.summable_probability_weighted {ι : Type*} {p f : ι → ℝ} {M : ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hp : HasSum p 1) (hf : ∀ i, |f i| ≤ M) :
    Summable (fun i => p i * f i) := by sorry
