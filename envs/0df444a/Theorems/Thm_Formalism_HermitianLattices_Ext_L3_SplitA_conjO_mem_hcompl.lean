-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitA_conjO_mem_hcompl
-- name    : Formalism.HermitianLattices.Ext.L3.SplitA.conjO_mem_hcompl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:40:09.729252+00:00
-- url     : https://prove2.me/theorems/9cb934b2-7d52-4622-91e6-f633cea2f343
-- title:
--   Split A: conj O mem hcompl
-- statement:
--   The Split A construction uses the conj O mem hcompl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ConjOMemHcompl.lean#L11-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ConjOMemHcompl.lean#L11-L26

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

theorem Formalism.HermitianLattices.Ext.L3.SplitA.conjO_mem_hcompl (p : Ideal (𝓞 K)) {s : 𝓞 K} (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p) :
    conjO K s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := by sorry
