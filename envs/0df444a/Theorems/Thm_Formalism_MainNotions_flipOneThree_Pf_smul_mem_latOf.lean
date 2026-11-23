-- Prove2me | Theorems.Thm_Formalism_MainNotions_flipOneThree_Pf_smul_mem_latOf
-- name    : Formalism.MainNotions.flipOneThree.Pf.smul_mem_latOf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:55:17.86809+00:00
-- url     : https://prove2.me/theorems/3791a81c-9dd0-415a-9cc1-88caaebbec9c
-- title:
--   Pf: smul mem lat Of
-- statement:
--   The Pf construction uses the smul mem lat Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ColumnSpanDensity/HarProjEqZeroIff.lean#L9-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ColumnSpanDensity/HarProjEqZeroIff.lean#L9-L17

import Definitions.Def_Formalism_PolynomialDimension_FinalHar
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_HarProjEqZeroIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.flipOneThree Formalism.MainNotions.flipOneThree.Pf
open Formalism.CountingSumsFrames MvPolynomial

theorem Formalism.MainNotions.flipOneThree.Pf.smul_mem_latOf {K : Type} [Field K] {k : ℕ} (R : Subring K) (g : GL (Fin k) K) {c : K} (hc : c ∈ R)
    {f : PolXY K k} (hf : f ∈ latOf g (GaussLat R)) : c • f ∈ latOf g (GaussLat R) := by sorry
