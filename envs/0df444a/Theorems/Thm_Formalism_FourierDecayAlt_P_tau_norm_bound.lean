-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_tau_norm_bound
-- name    : Formalism.FourierDecayAlt.P.tau_norm_bound
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:36:40.512626+00:00
-- url     : https://prove2.me/theorems/1014b5df-139c-5f7f-9438-d093d0c87af9
-- title:
--   P: tau norm bound
-- statement:
--   The P construction uses the tau norm bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormEntryBounds.lean#L53-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormEntryBounds.lean#L53-L141

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryMinorBounds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZhatSectionExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormEntryBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x2 C2x5 HermitianXiVector UnipotentSums EntryMinorBounds
open NormEntryBounds

theorem Formalism.FourierDecayAlt.P.tau_norm_bound : C2.TauBound := by sorry
