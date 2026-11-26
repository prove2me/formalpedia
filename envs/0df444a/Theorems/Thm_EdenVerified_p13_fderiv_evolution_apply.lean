-- Prove2me | Theorems.Thm_EdenVerified_p13_fderiv_evolution_apply
-- name    : EdenVerified.p13_fderiv_evolution_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:44:17.544888+00:00
-- url     : https://prove2.me/theorems/b0e461c5-119a-4f66-a1a8-b6fef146bada
-- title:
--   Eden Verified: p13 fderiv evolution apply
-- statement:
--   The Eden Verified construction uses the p13 fderiv evolution apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1395-L1403
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1395-L1403

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p13_fderiv_evolution_apply :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p v : PhaseSpace),
    fderiv ℝ (evolution c t) p v =
      !₂[planarDerivativeX 1 t (p 0) (p 1) (v 0) (v 1),
         planarDerivativeY 1 t (p 0) (p 1) (v 0) (v 1),
         planarDerivativeX (Real.sqrt 2) t (p 2) (p 3) (v 2) (v 3),
         planarDerivativeY (Real.sqrt 2) t (p 2) (p 3) (v 2) (v 3),
         Real.exp (-c * t) * v 4] := by sorry
