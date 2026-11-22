-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_rho_eq
-- name    : Formalism.FourierDecayAlt.P.Mx3.rho_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:45:24.768798+00:00
-- url     : https://prove2.me/theorems/e7607a37-f2b4-485a-b0fd-3d06f382b83c
-- title:
--   Mx3: rho eq
-- statement:
--   The Mx3 construction uses the rho eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/InterlaceSignTwo.lean#L7-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/InterlaceSignTwo.lean#L7-L9

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

theorem Formalism.FourierDecayAlt.P.Mx3.rho_eq (P : Par) (π : Ty P) (i : ℕ) (h : 1 ≤ i ∧ i ≤ P.k - 1) :
    rho P π i = P.lo i + (((π ⟨i - 1, by omega⟩ : Fin _) : ℕ) : ℝ) := by sorry
