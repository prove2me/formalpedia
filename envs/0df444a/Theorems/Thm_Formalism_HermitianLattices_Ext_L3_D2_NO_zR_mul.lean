-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_NO_zR_mul
-- name    : Formalism.HermitianLattices.Ext.L3.D2.NO.zR_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T09:44:50.649055+00:00
-- url     : https://prove2.me/theorems/dcebbe09-7e12-4ef9-932b-c389d0be14b6
-- title:
--   NO: z R mul
-- statement:
--   The NO construction uses the z R mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsMulEqUnifPow.lean#L30-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsMulEqUnifPow.lean#L30-L37

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulEqUnifPow
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
open Formalism.HermitianLattices.Ext.L3.D2.NO

theorem Formalism.HermitianLattices.Ext.L3.D2.NO.zR_mul (𝔭 : Ideal (𝓞 F)) (z w : K) :
    zR 𝔭 (z * w) = (zR 𝔭 w).map (AddMonoidHom.mulLeft z) := by sorry
