-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_relIndex_sesqL_eq_sq
-- name    : Formalism.HermitianLattices.Ext.L3.D2.relIndex_sesqL_eq_sq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T09:55:09.071134+00:00
-- url     : https://prove2.me/theorems/762827c4-8125-4c5b-a06b-bb3e8379ecfe
-- title:
--   D2: rel Index sesq L eq sq
-- statement:
--   The D2 construction uses the rel Index sesq L eq sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/RelIndexEqMapMulKer.lean#L210-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/RelIndexEqMapMulKer.lean#L210-L221

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulSpanIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MulMemPrimePower
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RelIndexEqMapMulKer
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

theorem Formalism.HermitianLattices.Ext.L3.D2.relIndex_sesqL_eq_sq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (A₀ B₀ : Submodule (𝓞 K) V)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k k' : ℕ}
    (hle : sesqL (locF 𝔭 B₀) 𝔭 k' ≤ sesqL (locF 𝔭 A₀) 𝔭 k) :
    (sesqL (locF 𝔭 B₀) 𝔭 k').relIndex (sesqL (locF 𝔭 A₀) 𝔭 k) =
      (hermL (locF 𝔭 B₀) 𝔭 k').relIndex (hermL (locF 𝔭 A₀) 𝔭 k) ^ 2 := by sorry
