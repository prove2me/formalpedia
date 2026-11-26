-- Prove2me | Theorems.Thm_EdenVerified_p09_toMatrix_fderiv_planarVectorField
-- name    : EdenVerified.p09_toMatrix_fderiv_planarVectorField
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:33:43.908717+00:00
-- url     : https://prove2.me/theorems/1b54b092-88df-4eed-b641-69a1c38bff9a
-- title:
--   Eden Verified: p09 to Matrix fderiv planar Vector Field
-- statement:
--   The Eden Verified construction uses the p09 to Matrix fderiv planar Vector Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L967-L976
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L967-L976

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p09_toMatrix_fderiv_planarVectorField :
    ∀ (Ω : ℝ) (p : PlanarSpace),
    (fderiv ℝ (planarVectorField Ω) p).toLinearMap.toMatrix
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis =
      q (p 0 ^ 2 + p 1 ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        (2 * deriv q (p 0 ^ 2 + p 1 ^ 2)) •
          Matrix.vecMulVec (fun i => p i) (fun i => p i) +
        Ω • !![0, -1; 1, 0] := by sorry
