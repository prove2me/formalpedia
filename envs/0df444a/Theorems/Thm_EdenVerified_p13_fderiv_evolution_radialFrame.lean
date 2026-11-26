-- Prove2me | Theorems.Thm_EdenVerified_p13_fderiv_evolution_radialFrame
-- name    : EdenVerified.p13_fderiv_evolution_radialFrame
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:45:46.840574+00:00
-- url     : https://prove2.me/theorems/02ccaf71-f9a1-49fa-99d7-7f7c70ff3659
-- title:
--   Eden Verified: p13 fderiv evolution radial Frame
-- statement:
--   The Eden Verified construction uses the p13 fderiv evolution radial Frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1405-L1409
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1405-L1409

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p13_fderiv_evolution_radialFrame :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p v : PhaseSpace),
    fderiv ℝ (evolution c t) p (radialFrame p v) =
      angularRotation t (radialFrame p (diagonalLinear (derivativeFactors c t p) v)) := by sorry
