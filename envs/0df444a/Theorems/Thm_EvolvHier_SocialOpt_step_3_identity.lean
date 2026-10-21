-- Prove2me | Theorems.Thm_EvolvHier_SocialOpt_step_3_identity
-- name    : EvolvHier.SocialOpt.step_3_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:23.251123+00:00
-- url     : https://prove2.me/theorems/819ccded-9aab-403f-8b0a-3e2398cec82f
-- title:
--   Step 3 — weighted gross returns equal length minus one
-- statement:
--   For a scheme with no self-transfer by agents $i\geq1$, the weighted gross returns conditional on each next arrival account for every arrival after agent 0:
--
--   $$1+\sum_{i\geq0}w_{i+1}(x)E_i^*(t,x)=L(x).$$
--
--   The identity connects incentive payments to the expected length of the hierarchy.
--
--   **Formalization Note** The sum is in extended nonnegative reals. The no-self-transfer condition is the condition under which the paper invokes this identity.
-- source:
--   Hougaard, Moreno-Ternero & Østerdal, Optimal Management of Evolving Hierarchies, UPO WP ECON 21.15 (Aug. 3, 2021; Manag. Sci. doi:10.1287/mnsc.2021.4185), proof of Theorem 2, Step 3, p. 25

import Mathlib
import Definitions.Def_EvolvHier_SocialOpt_Setting

namespace EvolvHier.SocialOpt

/-- The length identity in the proof of Theorem 2, Step 3. -/
theorem step_3_identity (T : Technology) (t : ℕ → ℕ → ℝ) (x : ℕ → ℝ)
    (ht : IsScheme t) (hx : IsProfile x)
    (hdiag : ∀ i, 1 ≤ i → t i i = 0) :
    1 + ∑' i, ENNReal.ofReal (w T x (i + 1)) * Estar T t x i = L T x := by sorry

end EvolvHier.SocialOpt
