-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_nO_mul
-- name    : Formalism.HermitianLattices.Ext.L3.D2.nO_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T09:43:27.523155+00:00
-- url     : https://prove2.me/theorems/13d50626-4460-4a87-8703-1bb857606819
-- title:
--   D2: n O mul
-- statement:
--   The D2 construction uses the n O mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsMulEqUnifPow.lean#L115-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsMulEqUnifPow.lean#L115-L123

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
open NO

theorem Formalism.HermitianLattices.Ext.L3.D2.nO_mul {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {z w : K} (hz : z ∈ pK K 𝔭 0) (hz0 : z ≠ 0)
    (hw : w ∈ pK K 𝔭 0) : nO 𝔭 (z * w) = nO 𝔭 z * nO 𝔭 w := by sorry
