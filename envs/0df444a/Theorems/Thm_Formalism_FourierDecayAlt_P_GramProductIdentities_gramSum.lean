-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GramProductIdentities_gramSum
-- name    : Formalism.FourierDecayAlt.P.GramProductIdentities.gramSum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:30.52222+00:00
-- url     : https://prove2.me/theorems/01c74f46-75cf-49ca-b050-bfbe1cbe7a89
-- title:
--   Gram Product Identities: gram Sum
-- statement:
--   The Gram Product Identities construction uses the gram Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramProductIdentities.lean#L86-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramProductIdentities.lean#L86-L106

import Definitions.Def_Formalism_HermitianCurvature_PositionExpansionTopCoefficients
import Definitions.Def_Lemmata_HermitianSesquilinear_ConjEqOfNonnegReal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GramProductIdentities
open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

theorem Formalism.FourierDecayAlt.P.GramProductIdentities.gramSum : GramSum := by sorry
