-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_algebraMap_ne_zero_of_mem_hcompl
-- name    : Formalism.HermitianLattices.Ext.L3.WA.algebraMap_ne_zero_of_mem_hcompl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:28:35.668294+00:00
-- url     : https://prove2.me/theorems/ecbcc9cd-e430-43d5-a5ab-208c8ff5722b
-- title:
--   WA: algebra Map ne zero of mem hcompl
-- statement:
--   The WA construction uses the algebra Map ne zero of mem hcompl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AlgebraMapNeZeroOfMemHcompl.lean#L69-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AlgebraMapNeZeroOfMemHcompl.lean#L69-L73

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

theorem Formalism.HermitianLattices.Ext.L3.WA.algebraMap_ne_zero_of_mem_hcompl {p : Ideal (𝓞 K)} (hp : p.IsPrime) {s : 𝓞 K}
    (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p) : algebraMap (𝓞 K) K s ≠ 0 := by sorry
