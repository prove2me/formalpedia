-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_rho_inj
-- name    : Formalism.FourierDecayAlt.P.Mx3.rho_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:45:40.462838+00:00
-- url     : https://prove2.me/theorems/72f37072-74b2-4538-b173-ea5cef3613c6
-- title:
--   Mx3: rho inj
-- statement:
--   The Mx3 construction uses the rho inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/InterlaceSignTwo.lean#L296-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/InterlaceSignTwo.lean#L296-L301

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

theorem Formalism.FourierDecayAlt.P.Mx3.rho_inj (P : Par) (hP : P.OK) (π : Ty P) (i j : ℕ) (hi : i ∈ Icc 1 (P.k - 1)) (hj : j ∈ Icc 1 (P.k - 1))
    (hij : i < j) : rho P π j < rho P π i := by sorry
