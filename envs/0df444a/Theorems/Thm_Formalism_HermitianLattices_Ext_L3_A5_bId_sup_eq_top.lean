-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_bId_sup_eq_top
-- name    : Formalism.HermitianLattices.Ext.L3.A5.bId_sup_eq_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:46:00.181104+00:00
-- url     : https://prove2.me/theorems/dfb9642d-facc-45d1-9c57-f4b9fd8a7779
-- title:
--   A5: b Id sup eq top
-- statement:
--   The A5 construction uses the b Id sup eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FinitePrimesOfMem.lean#L109-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FinitePrimesOfMem.lean#L109-L122

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFilterResCharLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SummableSqGeom
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinitePrimesOfMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.A5
variable {F : Type} [Field F] [NumberField F]

theorem Formalism.HermitianLattices.Ext.L3.A5.bId_sup_eq_top {v : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} →₀ ℕ}
    {𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}} (h𝔭 : 𝔭 ∉ v.support) : bId v ⊔ 𝔭.1 = ⊤ := by sorry
