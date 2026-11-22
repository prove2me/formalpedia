-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_mem_locRing
-- name    : Formalism.HermitianLattices.Ext.L3.WA.mem_locRing
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:28:19.405802+00:00
-- url     : https://prove2.me/theorems/a56b0770-d060-41e4-aacf-a3a7a514c007
-- title:
--   WA: mem loc Ring
-- statement:
--   The WA construction uses the mem loc Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AlgebraMapNeZeroOfMemHcompl.lean#L114-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AlgebraMapNeZeroOfMemHcompl.lean#L114-L115

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormOneOfPair
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapNeZeroOfMemHcompl
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.WA
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.HermitianLattices.Ext.L3.WA.mem_locRing (p : Ideal (𝓞 K)) (a : K) :
    a ∈ locRing p ↔ a ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := by sorry
