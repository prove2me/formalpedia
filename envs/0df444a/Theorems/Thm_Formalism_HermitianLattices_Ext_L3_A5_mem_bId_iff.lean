-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_mem_bId_iff
-- name    : Formalism.HermitianLattices.Ext.L3.A5.mem_bId_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:44:22.94945+00:00
-- url     : https://prove2.me/theorems/788e4457-87b4-4167-89eb-07e196021a4e
-- title:
--   A5: mem b Id iff
-- statement:
--   The A5 construction uses the mem b Id iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FinitePrimesOfMem.lean#L92-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FinitePrimesOfMem.lean#L92-L107

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

theorem Formalism.HermitianLattices.Ext.L3.A5.mem_bId_iff {n : 𝓞 F} (hn : n ≠ 0) (v : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} →₀ ℕ) :
    n ∈ bId v ↔ v ≤ valF n := by sorry
