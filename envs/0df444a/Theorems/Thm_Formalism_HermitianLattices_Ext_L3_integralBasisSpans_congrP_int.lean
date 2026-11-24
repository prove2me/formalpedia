-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_congrP_int
-- name    : Formalism.HermitianLattices.Ext.L3.integralBasisSpans.congrP_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:51:47.103228+00:00
-- url     : https://prove2.me/theorems/e1df7471-7006-456a-a764-9d1ada583f80
-- title:
--   integral Basis Spans: congr P int
-- statement:
--   The integral Basis Spans construction uses the congr P int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LocalDensitySixth.lean#L46-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LocalDensitySixth.lean#L46-L59

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardQuotExtPPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.integralBasisSpans
open LocalSpans idealPowerSpanBounds localizedQuotients
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem Formalism.HermitianLattices.Ext.L3.integralBasisSpans.congrP_int {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) (a c : 𝓞 K) :
    CongrP 𝔭 k (algebraMap (𝓞 K) K a) (algebraMap (𝓞 K) K c) ↔
      Ideal.Quotient.mk (extP K 𝔭 ^ k) a = Ideal.Quotient.mk (extP K 𝔭 ^ k) c := by sorry
