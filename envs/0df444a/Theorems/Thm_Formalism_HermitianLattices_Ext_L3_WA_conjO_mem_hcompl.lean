-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_conjO_mem_hcompl
-- name    : Formalism.HermitianLattices.Ext.L3.WA.conjO_mem_hcompl
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:42:34.640716+00:00
-- url     : https://prove2.me/theorems/e1cc0983-9779-47a4-b694-dfcdda875bda
-- title:
--   WA: conj O mem hcompl
-- statement:
--   The WA construction uses the conj O mem hcompl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AlgebraMapNeZeroOfMemHcompl.lean#L59-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AlgebraMapNeZeroOfMemHcompl.lean#L59-L67

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

theorem Formalism.HermitianLattices.Ext.L3.WA.conjO_mem_hcompl {p : Ideal (𝓞 K)} {s : 𝓞 K} (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p) :
    conjO K s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := by sorry
