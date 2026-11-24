-- Prove2me | Theorems.Thm_Formalism_GM_GaussNormRoots_vmin_step
-- name    : Formalism.GM.GaussNormRoots.vmin_step
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:16:13.393807+00:00
-- url     : https://prove2.me/theorems/4353017f-4673-4dc2-8a4b-ccf0d3152e74
-- title:
--   Gauss Norm Roots: vmin step
-- statement:
--   The Gauss Norm Roots construction uses the vmin step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieRoots.lean#L111-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieRoots.lean#L111-L136

import Definitions.Def_Formalism_MahlerMeasure_LieRoots
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieRoots
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Finset Polynomial
open Formalism.GM.GaussNormRoots

theorem Formalism.GM.GaussNormRoots.vmin_step (p : ℕ) (hp1 : (1 : ℝ) < p) (h : ℕ) (E : ℝ) (hE : 0 ≤ E) (u : ℝ) (_hu : 0 ≤ u)
    [Decidable (u ≤ (p : ℝ) ^ (-(h : ℤ)))] :
    -Real.logb p (max u ((p : ℝ) ^ (-((h : ℝ) + E)))) ≤
      -Real.logb p (max u ((p : ℝ) ^ (-(h : ℤ)))) + E * (if u ≤ (p : ℝ) ^ (-(h : ℤ)) then 1 else 0) := by sorry
