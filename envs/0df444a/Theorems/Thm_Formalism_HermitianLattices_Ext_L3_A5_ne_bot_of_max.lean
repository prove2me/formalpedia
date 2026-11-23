-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_ne_bot_of_max
-- name    : Formalism.HermitianLattices.Ext.L3.A5.ne_bot_of_max
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:41:41.454364+00:00
-- url     : https://prove2.me/theorems/b616e38e-d701-4bb2-80ee-33f9765dcf38
-- title:
--   A5: ne bot of max
-- statement:
--   The A5 construction uses the ne bot of max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FinitePrimesOfMem.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FinitePrimesOfMem.lean#L13-L14

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

theorem Formalism.HermitianLattices.Ext.L3.A5.ne_bot_of_max {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 𝔭 ≠ ⊥ := by sorry
