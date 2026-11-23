-- Prove2me | Theorems.Thm_Formalism_GM_GaussNormRoots_gaussR_C
-- name    : Formalism.GM.GaussNormRoots.gaussR_C
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:46:42.118796+00:00
-- url     : https://prove2.me/theorems/d37d903b-b72f-4120-8332-560852b14960
-- title:
--   Gauss Norm Roots: gauss R C
-- statement:
--   The Gauss Norm Roots construction uses the gauss R C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieRoots.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieRoots.lean#L22-L24

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

theorem Formalism.GM.GaussNormRoots.gaussR_C (ρ : NNReal) (a : K) : gaussR ρ (Polynomial.C a) = ‖a‖₊ := by sorry
