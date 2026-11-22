-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_mem_conjIdeal_iff
-- name    : Formalism.HermitianLattices.Ext.L3.WA.mem_conjIdeal_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:40:23.385936+00:00
-- url     : https://prove2.me/theorems/0adbf954-2b3b-4fe0-8624-a8bc8414344c
-- title:
--   WA: mem conj Ideal iff
-- statement:
--   The WA construction uses the mem conj Ideal iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AlgebraMapNeZeroOfMemHcompl.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AlgebraMapNeZeroOfMemHcompl.lean#L19-L21

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

theorem Formalism.HermitianLattices.Ext.L3.WA.mem_conjIdeal_iff (p : Ideal (𝓞 K)) (r : 𝓞 K) :
    r ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) p ↔ conjO K r ∈ p := by sorry
