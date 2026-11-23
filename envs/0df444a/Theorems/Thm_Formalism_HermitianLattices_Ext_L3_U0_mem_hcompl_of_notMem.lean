-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_mem_hcompl_of_notMem
-- name    : Formalism.HermitianLattices.Ext.L3.U0.mem_hcompl_of_notMem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:08:37.3338+00:00
-- url     : https://prove2.me/theorems/92ffe36f-3c60-4b03-94c5-d6b5aa13c9c9
-- title:
--   U0: mem hcompl of not Mem
-- statement:
--   The U0 construction uses the mem hcompl of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsFracOfFixed.lean#L20-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsFracOfFixed.lean#L20-L32

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormRepresentation
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsFracOfFixed
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0
open WA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem Formalism.HermitianLattices.Ext.L3.U0.mem_hcompl_of_notMem (hF : IsFixF K F) {P : Ideal (𝓞 K)} (hP : P.IsPrime) {t : 𝓞 F}
    (ht : t ∉ P.comap (algebraMap (𝓞 F) (𝓞 K))) :
    algebraMap (𝓞 F) (𝓞 K) t ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P := by sorry
