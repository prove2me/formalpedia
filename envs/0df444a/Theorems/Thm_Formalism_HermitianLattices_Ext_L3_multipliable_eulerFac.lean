-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_multipliable_eulerFac
-- name    : Formalism.HermitianLattices.Ext.L3.multipliable_eulerFac
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:33:52.904681+00:00
-- url     : https://prove2.me/theorems/fa9d917b-ced3-489a-b0ec-0b691cde35ed
-- title:
--   L3: multipliable euler Fac
-- statement:
--   The L3 construction uses the multipliable euler Fac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/EulerFacMulConjInvSplit.lean#L126-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/EulerFacMulConjInvSplit.lean#L126-L129

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

theorem Formalism.HermitianLattices.Ext.L3.multipliable_eulerFac (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (M : ℕ) (hM : 2 ≤ M) :
    Multipliable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => Formalism.HermitianLatticesTheory.eulerFac K M P.1) := by sorry
