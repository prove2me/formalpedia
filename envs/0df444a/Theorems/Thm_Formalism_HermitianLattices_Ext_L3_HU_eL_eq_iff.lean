-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_eL_eq_iff
-- name    : Formalism.HermitianLattices.Ext.L3.HU.eL_eq_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:52.236009+00:00
-- url     : https://prove2.me/theorems/bfb743f6-2a77-4cdb-b3d4-f40caa0932fd
-- title:
--   HU: e L eq iff
-- statement:
--   The HU construction uses the e L eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CoeCmbSingle.lean#L111-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CoeCmbSingle.lean#L111-L133

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMatrixOfIsom
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CoeCmbSingle
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
open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

theorem Formalism.HermitianLattices.Ext.L3.HU.eL_eq_iff {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) [𝔭.IsPrime] (b : Basis κ K V) (k : ℕ)
    (X : Module.End (𝓞 K) (QA 𝔭 b k)) (Y : Matrix κ κ (𝓞 K)) :
    eL h𝔭 b k X = Y.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) ↔
      ∀ i, X (Submodule.Quotient.mk (inA 𝔭 b (cmb b (Pi.single i 1)))) =
        Submodule.Quotient.mk (inA 𝔭 b (cmb b fun l => Y l i)) := by sorry
