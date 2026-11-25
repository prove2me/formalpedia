-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BrB_finite_between
-- name    : Formalism.HermitianLattices.Ext.L3.BrB.finite_between
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:42:59.327916+00:00
-- url     : https://prove2.me/theorems/d4fb0075-9a9a-4c2d-b4dc-f5d305defbe9
-- title:
--   Br B: finite between
-- statement:
--   The Br B construction uses the finite between property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsLocReps.lean#L16-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsLocReps.lean#L16-L35

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsIntegralLatOfForall
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_FinIntermediate
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocReps
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BrB
variable {K V : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem Formalism.HermitianLattices.Ext.L3.BrB.finite_between {N D : Submodule (𝓞 K) V} (hN : Submodule.IsLattice K N)
    (hD : Submodule.IsLattice K D) (hND : N ≤ D) :
    {Λ : Submodule (𝓞 K) V | N ≤ Λ ∧ Λ ≤ D}.Finite := by sorry
