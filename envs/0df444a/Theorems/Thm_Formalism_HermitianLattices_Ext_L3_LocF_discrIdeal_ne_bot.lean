-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_discrIdeal_ne_bot
-- name    : Formalism.HermitianLattices.Ext.L3.LocF.discrIdeal_ne_bot
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:50:34.166845+00:00
-- url     : https://prove2.me/theorems/5ffeb301-19da-431b-a3c3-5e979b2fa248
-- title:
--   Loc F: discr Ideal ne bot
-- statement:
--   The Loc F construction uses the discr Ideal ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/VdEqZeroOfNotLe.lean#L33-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/VdEqZeroOfNotLe.lean#L33-L48

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapIntCastSmul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LinearIndependentOfGramDetNeZero
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VdEqZeroOfNotLe
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LocF
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem Formalism.HermitianLattices.Ext.L3.LocF.discrIdeal_ne_bot [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hd : ∀ x, h x x = 0 → x = 0) {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L)
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) : discrIdeal h L ≠ ⊥ := by sorry
