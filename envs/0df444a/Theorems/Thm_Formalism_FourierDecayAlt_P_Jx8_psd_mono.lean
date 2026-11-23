-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_psd_mono
-- name    : Formalism.FourierDecayAlt.P.Jx8.psd_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:38.490694+00:00
-- url     : https://prove2.me/theorems/3030263c-78ca-4c53-8b1d-c0a017e9a7f5
-- title:
--   Jx8: psd mono
-- statement:
--   The Jx8 construction uses the psd mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OutsideSystemsBound.lean#L216-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OutsideSystemsBound.lean#L216-L218

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx8
variable {α : Type}

theorem Formalism.FourierDecayAlt.P.Jx8.psd_mono {F G : Finset α} (h : F ⊆ G) {k : α → α → ℂ} (hk : TB.PSDOn G k) : TB.PSDOn F k := by sorry
