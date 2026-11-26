-- Prove2me | Theorems.Thm_EdenVerified_p11_fderiv_planarEvolution_origin
-- name    : EdenVerified.p11_fderiv_planarEvolution_origin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:33:32.130879+00:00
-- url     : https://prove2.me/theorems/685c8e04-f486-5079-8c88-48b9c68d294c
-- title:
--   Eden Verified: p11 fderiv planar Evolution origin
-- statement:
--   The Eden Verified construction uses the p11 fderiv planar Evolution origin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1027-L1031
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1027-L1031

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p11_fderiv_planarEvolution_origin :
    ∀ (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t) (v : PlanarSpace),
    fderiv ℝ (planarEvolution Ω t) 0 v =
      Real.exp (-2 * t) • planarAngularRotation Ω t v := by sorry
