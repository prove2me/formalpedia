-- Prove2me | Theorems.Thm_EdenVerified_D08_singular_value_function
-- name    : EdenVerified.D08_singular_value_function
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:26:27.852002+00:00
-- url     : https://prove2.me/theorems/0c4347e0-7d0a-5b3e-a61e-ca924ce4ec70
-- title:
--   Eden Verified: D08 singular value function
-- statement:
--   The fractional formula and determinant endpoint agree continuously.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L594-L604
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L594-L604

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.D08_singular_value_function (M : PhaseSpace →ₗ[ℝ] PhaseSpace)
    (hM : Function.Injective M) :
    singularValueFunction M 0 = 1 ∧
    (∀ k : ℕ, k < 5 → ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      singularValueFunction M ((k : ℝ) + α) =
        (∏ i ∈ Finset.range k, M.singularValues i) * M.singularValues k ^ α) ∧
    singularValueFunction M 5 = |M.det| ∧
    ContinuousOn (singularValueFunction M) (Icc 0 5) := by sorry
