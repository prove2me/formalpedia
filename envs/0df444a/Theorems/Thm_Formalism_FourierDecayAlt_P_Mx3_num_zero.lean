-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_num_zero
-- name    : Formalism.FourierDecayAlt.P.Mx3.num_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:00.843053+00:00
-- url     : https://prove2.me/theorems/708a670c-9858-4d54-a8b8-ed0e8f8e963c
-- title:
--   Mx3: num zero
-- statement:
--   The Mx3 construction uses the num zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/InterlaceSignTwo.lean#L269-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/InterlaceSignTwo.lean#L269-L278

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx3

theorem Formalism.FourierDecayAlt.P.Mx3.num_zero (P : Par) (hP : P.OK) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (π : Ty P) (h : ¬ ∃ π', Up P l π π') :
    I.qpoly P.k P.T P.T' P.u P.u' (-rho P π l - 1) = 0 := by sorry
