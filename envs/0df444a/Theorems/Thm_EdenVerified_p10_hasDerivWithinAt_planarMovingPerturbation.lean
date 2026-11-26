-- Prove2me | Theorems.Thm_EdenVerified_p10_hasDerivWithinAt_planarMovingPerturbation
-- name    : EdenVerified.p10_hasDerivWithinAt_planarMovingPerturbation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:33:41.813856+00:00
-- url     : https://prove2.me/theorems/d080cd2b-d611-45de-b05f-08c7b80aa6c5
-- title:
--   Eden Verified: p10 has Deriv Within At planar Moving Perturbation
-- statement:
--   The Eden Verified construction uses the p10 has Deriv Within At planar Moving Perturbation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1003-L1011
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1003-L1011

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p10_hasDerivWithinAt_planarMovingPerturbation :
    ∀ (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p v : PlanarSpace),
    HasDerivWithinAt (fun τ => planarMovingPerturbation Ω τ p v)
      (!₂[radialRate (planarEvolution Ω t p 0 ^ 2 + planarEvolution Ω t p 1 ^ 2) *
          planarMovingPerturbation Ω t p v 0,
        tangentialRate (planarEvolution Ω t p 0 ^ 2 + planarEvolution Ω t p 1 ^ 2) *
          planarMovingPerturbation Ω t p v 1]) (Set.Ici 0) t := by sorry
