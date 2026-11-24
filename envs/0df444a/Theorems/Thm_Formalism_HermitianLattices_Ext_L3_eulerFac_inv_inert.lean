-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_eulerFac_inv_inert
-- name    : Formalism.HermitianLattices.Ext.L3.eulerFac_inv_inert
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:56.426859+00:00
-- url     : https://prove2.me/theorems/9f65dcd5-bdad-4dce-989d-c9e0c15b2e4f
-- title:
--   L3: euler Fac inv inert
-- statement:
--   The L3 construction uses the euler Fac inv inert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/EulerFacMulConjInvSplit.lean#L106-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/EulerFacMulConjInvSplit.lean#L106-L111

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFilterResCharLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EulerFacMulConjInvSplit
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open IdealNormInequalities

theorem Formalism.HermitianLattices.Ext.L3.eulerFac_inv_inert (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) (M : ℕ) :
    (Formalism.HermitianLatticesTheory.eulerFac K M P)⁻¹ =
      1 - (-1 : ℝ) ^ M * Real.sqrt (Ideal.absNorm P : ℝ) ^ (-(M : ℤ)) := by sorry
