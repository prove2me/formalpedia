-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_card_skew_lift
-- name    : Formalism.HermitianLattices.Ext.L3.HU.card_skew_lift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:57:08.415984+00:00
-- url     : https://prove2.me/theorems/e67d195e-5c2f-429d-98ff-44425fbebff4
-- title:
--   HU: card skew lift
-- statement:
--   The HU construction uses the card skew lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsSkewValue.lean#L17-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsSkewValue.lean#L17-L72

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsAddConjTransposeEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSkewValue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open HermitianSublattices idealPowerSpanBounds
variable {A A' : Type*} [CommRing A] [StarRing A] [CommRing A'] [StarRing A']
variable {m : Type*} [Fintype m] [DecidableEq m]

theorem Formalism.HermitianLattices.Ext.L3.HU.card_skew_lift [Finite A] (π : A →+* A') (hπ : Function.Surjective π)
    (hπs : ∀ a, π (star a) = star (π a)) (H : Matrix m m A) (hH : Hᴴ = H)
    (hS : ∀ S ∈ hermSub m (RingHom.ker π), ∃ Y : Matrix m m A, H * Y + Yᴴ * H = S) :
    Nat.card {Y : Matrix m m A // H * Y + Yᴴ * H = 0} * Nat.card (hermSub m (RingHom.ker π)) =
      Nat.card (entSub m m (RingHom.ker π)) *
        Nat.card {Y' : Matrix m m A' // H.map π * Y' + Y'ᴴ * H.map π = 0} := by sorry
