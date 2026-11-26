-- Prove2me | Theorems.Thm_EdenVerified_p10_fderiv_planarEvolution_orthogonal_decomposition
-- name    : EdenVerified.p10_fderiv_planarEvolution_orthogonal_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:34:34.17181+00:00
-- url     : https://prove2.me/theorems/a0db9364-5857-4d08-b6a5-452899b78f99
-- title:
--   Eden Verified: p10 fderiv planar Evolution orthogonal decomposition
-- statement:
--   The Eden Verified construction uses the p10 fderiv planar Evolution orthogonal decomposition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L980-L986
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L980-L986

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p10_fderiv_planarEvolution_orthogonal_decomposition :
    ∀ (Ω : ℝ) {t : ℝ}
    (ht : 0 ≤ t) (p : PlanarSpace),
    (fderiv ℝ (planarEvolution Ω t) p).toLinearMap =
      ((planarRadialFrame p).trans (planarAngularRotation Ω t)).toLinearMap ∘ₗ
        planarDiagonal (planarFactors t p) ∘ₗ (planarRadialFrame p).symm.toLinearMap := by sorry
