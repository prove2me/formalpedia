-- Prove2me | Theorems.Thm_Formalism_GM_GaussNormRoots_gaussR_lin
-- name    : Formalism.GM.GaussNormRoots.gaussR_lin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:51.855527+00:00
-- url     : https://prove2.me/theorems/a97cefd8-cdd6-4f14-a3f9-dac11da6b822
-- title:
--   Gauss Norm Roots: gauss R lin
-- statement:
--   The Gauss Norm Roots construction uses the gauss R lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieRoots.lean#L26-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieRoots.lean#L26-L33

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
variable {K : Type} [NormedField K]

theorem Formalism.GM.GaussNormRoots.gaussR_lin (ρ : NNReal) (q a : K) :
    gaussR ρ (Polynomial.C q * X + Polynomial.C a) = max ‖a‖₊ (‖q‖₊ * ρ) := by sorry
