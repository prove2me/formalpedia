-- Prove2me | Theorems.Thm_EdenVerified_p10_hasDerivAt_planarMovingPerturbation
-- name    : EdenVerified.p10_hasDerivAt_planarMovingPerturbation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:33:16.615819+00:00
-- url     : https://prove2.me/theorems/2b8ca21c-5709-5a77-9d4c-ab75b5dfd298
-- title:
--   Eden Verified: p10 has Deriv At planar Moving Perturbation
-- statement:
--   The Eden Verified construction uses the p10 has Deriv At planar Moving Perturbation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L993-L1001
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L993-L1001

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p10_hasDerivAt_planarMovingPerturbation :
    ∀ (Ω : ℝ) {t : ℝ} (ht : 0 < t)
    (p v : PlanarSpace),
    HasDerivAt (fun τ => planarMovingPerturbation Ω τ p v)
      (!₂[radialRate (planarEvolution Ω t p 0 ^ 2 + planarEvolution Ω t p 1 ^ 2) *
          planarMovingPerturbation Ω t p v 0,
        tangentialRate (planarEvolution Ω t p 0 ^ 2 + planarEvolution Ω t p 1 ^ 2) *
          planarMovingPerturbation Ω t p v 1]) t := by sorry
