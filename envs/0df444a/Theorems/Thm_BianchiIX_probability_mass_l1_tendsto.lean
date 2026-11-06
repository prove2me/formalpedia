-- Prove2me | Theorems.Thm_BianchiIX_probability_mass_l1_tendsto
-- name    : BianchiIX.probability_mass_l1_tendsto
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T19:10:24.621032+00:00
-- url     : https://prove2.me/theorems/aaec31c0-47bd-45f1-9578-8f6e6cfad2fc
-- title:
--   Pointwise convergence of probability masses implies convergence in l1
-- statement:
--   Let $p_n,q:I\to\mathbb R$ be nonnegative probability masses,
--   each with convergent sum one. If $p_n(i)\to q_i$ for every $i$, then
--   $$\sum_{i\in I}|p_n(i)-q_i|\longrightarrow0.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/DiscreteMass.lean#L29-L45

import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace BianchiIX
end BianchiIX

open Filter
open scoped Topology
open BianchiIX

theorem BianchiIX.probability_mass_l1_tendsto {ι : Type*} {p : ℕ → ι → ℝ} {q : ι → ℝ}
    (hp0 : ∀ n i, 0 ≤ p n i) (hq0 : ∀ i, 0 ≤ q i)
    (hp : ∀ n, HasSum (p n) 1) (hq : HasSum q 1)
    (hpoint : ∀ i, Tendsto (fun n => p n i) atTop (𝓝 (q i))) :
    Tendsto (fun n => ∑' i, |p n i - q i|) atTop (𝓝 0) := by sorry
