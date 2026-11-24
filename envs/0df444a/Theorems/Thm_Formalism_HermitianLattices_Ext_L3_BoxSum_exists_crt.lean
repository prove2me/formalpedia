-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_exists_crt
-- name    : Formalism.HermitianLattices.Ext.L3.BoxSum.exists_crt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:47:22.643599+00:00
-- url     : https://prove2.me/theorems/aa9ea31c-061d-49bb-a802-2e1b8fcad399
-- title:
--   Box Sum: exists crt
-- statement:
--   The Box Sum construction uses the exists crt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/TendstoSumPeriodic.lean#L15-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/TendstoSumPeriodic.lean#L15-L27

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoSumCoset
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoSumPeriodic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter Topology
open scoped Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BoxSum
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem Formalism.HermitianLattices.Ext.L3.BoxSum.exists_crt {b 𝔞 : Ideal (𝓞 F)} (hco : b ⊔ 𝔞 = ⊤) (x₀ : 𝓞 F) (c : 𝓞 F ⧸ 𝔞) :
    ∃ x : 𝓞 F, x - x₀ ∈ b ∧ Ideal.Quotient.mk 𝔞 x = c := by sorry
