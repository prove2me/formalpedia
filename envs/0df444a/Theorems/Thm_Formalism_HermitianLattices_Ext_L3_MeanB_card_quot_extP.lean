-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_card_quot_extP
-- name    : Formalism.HermitianLattices.Ext.L3.MeanB.card_quot_extP
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:13:46.264395+00:00
-- url     : https://prove2.me/theorems/07c7275b-a3df-4c01-9d1d-9fe4a62c7486
-- title:
--   Mean B: card quot ext P
-- statement:
--   The Mean B construction uses the card quot ext P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/StarAlgebraMap.lean#L66-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/StarAlgebraMap.lean#L66-L129

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulSubOneMemPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.MeanB
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem Formalism.HermitianLattices.Ext.L3.MeanB.card_quot_extP (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    Nat.card (↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) =
      Ideal.absNorm 𝔭 ^ (2 * finrank K V * k) := by sorry
