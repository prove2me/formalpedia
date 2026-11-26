-- Prove2me | Theorems.Thm_EdenVerified_p13_fderiv_evolution_orthogonal_decomposition
-- name    : EdenVerified.p13_fderiv_evolution_orthogonal_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:44:40.74312+00:00
-- url     : https://prove2.me/theorems/58536dec-9e37-585d-9680-943573c922e3
-- title:
--   Eden Verified: p13 fderiv evolution orthogonal decomposition
-- statement:
--   The Eden Verified construction uses the p13 fderiv evolution orthogonal decomposition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1411-L1419
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1411-L1419

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p13_fderiv_evolution_orthogonal_decomposition :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace),
    (fderiv ℝ (evolution c t) p).toLinearMap =
      (angularRotation t).toLinearEquiv.toLinearMap ∘ₗ
        (radialFrame p).toLinearEquiv.toLinearMap ∘ₗ
          diagonalLinear (derivativeFactors c t p) ∘ₗ
            (radialFrame p).symm.toLinearEquiv.toLinearMap := by sorry
