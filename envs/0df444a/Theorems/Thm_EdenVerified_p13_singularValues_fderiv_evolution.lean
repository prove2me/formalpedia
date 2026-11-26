-- Prove2me | Theorems.Thm_EdenVerified_p13_singularValues_fderiv_evolution
-- name    : EdenVerified.p13_singularValues_fderiv_evolution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:44:54.464725+00:00
-- url     : https://prove2.me/theorems/64636c17-708f-442b-85e4-e8e8c7bbc049
-- title:
--   Eden Verified: p13 singular Values fderiv evolution
-- statement:
--   The Eden Verified construction uses the p13 singular Values fderiv evolution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1426-L1430
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1426-L1430

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p13_singularValues_fderiv_evolution :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace),
    Finset.univ.val.map (fun i : Fin 5 => (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) =
      Finset.univ.val.map (fun i : Fin 5 => derivativeFactors c t p i) := by sorry
