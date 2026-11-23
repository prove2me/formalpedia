-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_abs_smallTerm_le
-- name    : Formalism.HermitianLattices.Ext.L3.IdealNormInequalities.abs_smallTerm_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:11:48.587554+00:00
-- url     : https://prove2.me/theorems/36104921-c1e4-4e6a-9a38-fcfb711b6f00
-- title:
--   Ideal Norm Inequalities: abs small Term le
-- statement:
--   The Ideal Norm Inequalities construction uses the abs small Term le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/EulerFacMulConjInvSplit.lean#L56-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/EulerFacMulConjInvSplit.lean#L56-L69

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
open Formalism.HermitianLattices.Ext.L3.IdealNormInequalities

theorem Formalism.HermitianLattices.Ext.L3.IdealNormInequalities.abs_smallTerm_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {M : ℕ}
    (hM : 2 ≤ M) : |smallTerm M P| ≤ ((resChar P : ℝ) ^ 2)⁻¹ := by sorry
