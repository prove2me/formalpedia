-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_pull_lattice_typed
-- name    : Formalism.FourierDecayAlt.P.pull_lattice_typed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:18:49.765266+00:00
-- url     : https://prove2.me/theorems/13dbd9a3-125f-446f-a126-fa53912a4614
-- title:
--   P: pull lattice typed
-- statement:
--   The P construction uses the pull lattice typed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChebyshevToThreshold.lean#L104-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChebyshevToThreshold.lean#L104-L115

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevToThreshold
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P

theorem Formalism.FourierDecayAlt.P.pull_lattice_typed : Formalism.FourierDecayAlt.J.PullLatticeTyped := by sorry
