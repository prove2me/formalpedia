-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_unif_ne_zero
-- name    : Formalism.HermitianLattices.Ext.L3.D2.unif_ne_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T09:29:04.068686+00:00
-- url     : https://prove2.me/theorems/d924c910-857b-40f6-8e97-c4d523f1c9de
-- title:
--   D2: unif ne zero
-- statement:
--   The D2 construction uses the unif ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsMulDvdUnif.lean#L97-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsMulDvdUnif.lean#L97-L101

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ApplyMemSmul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem Formalism.HermitianLattices.Ext.L3.D2.unif_ne_zero {𝔭 : Ideal (𝓞 F)} {π : 𝓞 F} (hπ' : π ∉ 𝔭 ^ 2) :
    algebraMap F K (π : F) ≠ 0 := by sorry
