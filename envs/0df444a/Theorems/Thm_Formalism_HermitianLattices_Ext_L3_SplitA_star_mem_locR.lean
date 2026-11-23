-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitA_star_mem_locR
-- name    : Formalism.HermitianLattices.Ext.L3.SplitA.star_mem_locR
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:34:17.65364+00:00
-- url     : https://prove2.me/theorems/0bbed875-e2ff-4284-81b8-c59bc612b2dc
-- title:
--   Split A: star mem loc R
-- statement:
--   The Split A construction uses the star mem loc R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ConjOMemHcompl.lean#L31-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ConjOMemHcompl.lean#L31-L40

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjOMemHcompl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.SplitA
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.HermitianLattices.Ext.L3.SplitA.star_mem_locR (p : Ideal (𝓞 K)) {c : K} (hc : c ∈ Formalism.HermitianLatticesTheory.locR (K := K) p) :
    starRingEnd K c ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := by sorry
