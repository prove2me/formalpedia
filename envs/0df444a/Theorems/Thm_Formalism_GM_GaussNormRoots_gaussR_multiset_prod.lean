-- Prove2me | Theorems.Thm_Formalism_GM_GaussNormRoots_gaussR_multiset_prod
-- name    : Formalism.GM.GaussNormRoots.gaussR_multiset_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:48.225964+00:00
-- url     : https://prove2.me/theorems/70692ed1-8ee0-437b-aca2-2b8e832f9dcb
-- title:
--   Gauss Norm Roots: gauss R multiset prod
-- statement:
--   The Gauss Norm Roots construction uses the gauss R multiset prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieRoots.lean#L35-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieRoots.lean#L35-L45

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

theorem Formalism.GM.GaussNormRoots.gaussR_multiset_prod (hG : GaussMulRad) [IsUltrametricDist K] (ρ : NNReal) (hρ : 0 < ρ)
    (m : Multiset K) (f : K → K[X]) :
    gaussR ρ (m.map f).prod = (m.map (fun ζ => gaussR ρ (f ζ))).prod := by sorry
