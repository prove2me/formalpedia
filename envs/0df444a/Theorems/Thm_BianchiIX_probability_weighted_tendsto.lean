-- Prove2me | Theorems.Thm_BianchiIX_probability_weighted_tendsto
-- name    : BianchiIX.probability_weighted_tendsto
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T19:12:39.112447+00:00
-- url     : https://prove2.me/theorems/efec2fb5-e0c1-4c8c-843d-239c9d106ee2
-- title:
--   Convergence of bounded averages under pointwise convergence of probability masses
-- statement:
--   Let $p_n,q:I\to\mathbb R$ be nonnegative probability masses,
--   all with convergent sum one, and suppose $p_n(i)\to q_i$ for each $i$.
--   If $|f_i|\leq M$ for all $i$, then
--   $$\sum_i p_n(i)f_i\longrightarrow\sum_iq_if_i.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/DiscreteMass.lean#L77-L87

import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace BianchiIX
end BianchiIX

open Filter
open scoped Topology
open BianchiIX

theorem BianchiIX.probability_weighted_tendsto {ι : Type*} {p : ℕ → ι → ℝ} {q f : ι → ℝ} {M : ℝ}
    (hp0 : ∀ n i, 0 ≤ p n i) (hq0 : ∀ i, 0 ≤ q i)
    (hp : ∀ n, HasSum (p n) 1) (hq : HasSum q 1)
    (hpoint : ∀ i, Tendsto (fun n => p n i) atTop (𝓝 (q i)))
    (hf : ∀ i, |f i| ≤ M) :
    Tendsto (fun n => ∑' i, p n i * f i) atTop (𝓝 (∑' i, q i * f i)) := by sorry
