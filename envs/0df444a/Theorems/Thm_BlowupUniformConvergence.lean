-- Prove2me | Theorems.Thm_BlowupUniformConvergence
-- name    : BlowupUniformConvergence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:13:14.399838+00:00
-- url     : https://prove2.me/theorems/eb902e4e-009b-4179-9a9d-23f6a4a5c9dc
-- title:
--   Blowup Uniform Convergence: Blowup Uniform Convergence
-- statement:
--   Uniform convergence of the blow-ups on compact sets.  If `u` is `C^m` on an open
--   `Ω` containing `x₀` and every diagonal evaluation of `iteratedFDeriv ℝ j u x₀`
--   vanishes for `1 ≤ j < m`, then the rescalings
--   `u_r x = (u (x₀ + r • x) - u x₀) / r ^ m`
--   converge, uniformly on each closed ball `closedBall 0 R`, to the degree-`m`
--   homogeneous polynomial `P_m x = (1 / m !) * iteratedFDeriv ℝ m u x₀ (fun _ => x)` as
--   `r` decreases to `0` through positive values.
--
--   This is the `C^0` half of the paper's one-line assertion that `u_r → P_m` in
--   `C^1_loc`.  Everything here is a diagonal evaluation; no symmetry of the derivative
--   tensor and no polarization is used.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/BlowupUniformConvergence.lean#L14-L162
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/BlowupUniformConvergence.lean#L14-L162

import Definitions.Def_PHigherOrder_IteratedDerivAlongRay
import Definitions.Def_PHigherOrder_BlowupUniformConvergence
import Theorems.Thm_IteratedDerivAlongRay

set_option autoImplicit false

theorem BlowupUniformConvergence (Ω : Set Plane) (hΩ : IsOpen Ω) (u : Plane → ℝ)
    (x₀ : Plane) (hx₀ : x₀ ∈ Ω) (m : ℕ) (hm : 1 ≤ m)
    (hu : ContDiffOn ℝ (m : ℕ∞) u Ω)
    (hvan : ∀ j, 1 ≤ j → j < m → ∀ w : Plane, iteratedFDeriv ℝ j u x₀ (fun _ => w) = 0) :
    ∀ R : ℝ, 0 < R →
      TendstoUniformlyOn
        (fun (r : ℝ) (x : Plane) => (u (x₀ + r • x) - u x₀) / r ^ m)
        (fun x => (1 / (Nat.factorial m : ℝ)) * iteratedFDeriv ℝ m u x₀ (fun _ => x))
        (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (Metric.closedBall (0 : Plane) R) := by sorry
