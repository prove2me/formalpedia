-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitA_mul_mem_locR
-- name    : Formalism.HermitianLattices.Ext.L3.SplitA.mul_mem_locR
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:33:35.158451+00:00
-- url     : https://prove2.me/theorems/b223a5ca-9e0a-4080-aeb0-e19622de5513
-- title:
--   Split A: mul mem loc R
-- statement:
--   The Split A construction uses the mul mem loc R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ConjOMemHcompl.lean#L42-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ConjOMemHcompl.lean#L42-L52

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

theorem Formalism.HermitianLattices.Ext.L3.SplitA.mul_mem_locR (p : Ideal (𝓞 K)) {c d : K} (hc : c ∈ Formalism.HermitianLatticesTheory.locR (K := K) p)
    (hd : d ∈ Formalism.HermitianLatticesTheory.locR (K := K) p) : c * d ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := by sorry
