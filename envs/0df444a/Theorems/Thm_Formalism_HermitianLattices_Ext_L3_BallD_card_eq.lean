-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallD_card_eq
-- name    : Formalism.HermitianLattices.Ext.L3.BallD.card_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:09.954059+00:00
-- url     : https://prove2.me/theorems/4afcc8bf-4dbb-4816-9cfd-5560c9eea382
-- title:
--   Ball D: card eq
-- statement:
--   The Ball D construction uses the card eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MeasurableSetBallSet.lean#L125-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MeasurableSetBallSet.lean#L125-L159

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DiscreteTopologyOfZsmul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VolumeNormSqLeOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FundamentalDomainPiBasis
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthBasisMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CovolumeIntegerLatticeEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MeasurableSetBallSet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding MeasureTheory Module Pointwise
open scoped Classical
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BallD
open BallB BallC
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable [IsEmpty {w : InfinitePlace K // w.IsReal}] {h : V →ₗ⋆[K] V →ₗ[K] K}
  {b : Basis (Fin (finrank K V)) K V}

theorem Formalism.HermitianLattices.Ext.L3.BallD.card_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (L : Submodule (𝓞 K) V) {j : ℕ} (hj : 0 < j) :
    ballCount h L ((j : ℝ) ^ 2) =
      Nat.card ↑(ballSet h b ∩ (j : ℝ)⁻¹ • (lat b L : Set (Fin (finrank K V) → mixedSpace K))) := by sorry
