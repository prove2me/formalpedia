-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_vectorCountBounds_card_preimage_piQ
-- name    : Formalism.HermitianLattices.Ext.L3.vectorCountBounds.card_preimage_piQ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:24.746923+00:00
-- url     : https://prove2.me/theorems/ca18fad9-8b5a-48af-a4d4-a2dd19ee9809
-- title:
--   vector Count Bounds: card preimage pi Q
-- statement:
--   The vector Count Bounds construction uses the card preimage pi Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LocalDensityEleventh.lean#L106-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LocalDensityEleventh.lean#L106-L153

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNotMemOfSol
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEleventh
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.vectorCountBounds
open HermitianSublattices idealPowerSpanBounds traceDeterminantCongruences reductionMapsOfForms hermitianFormColumns
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [Fact (IsFixF K F)]
variable {m : Type} [Fintype m] [DecidableEq m]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem Formalism.HermitianLattices.Ext.L3.vectorCountBounds.card_preimage_piQ (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ)
    (T : (m → 𝓞 K ⧸ extP K 𝔭 ^ k) → Prop) :
    Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ (k + 1) // T (fun i => piQ K 𝔭 k (x i))} =
      Ideal.absNorm 𝔭 ^ (2 * Fintype.card m) * Nat.card {x // T x} := by sorry
