-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_C2x6_herm_ff
-- name    : Formalism.FourierDecayAlt.P.C2x6.herm_ff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:13:32.144116+00:00
-- url     : https://prove2.me/theorems/c2460e8c-2645-4ef4-a9ed-65b6ab1d7650
-- title:
--   C2x6: herm ff
-- statement:
--   The C2x6 construction uses the herm ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MajorantEstimate.lean#L14-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MajorantEstimate.lean#L14-L24

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFlagVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantEstimate
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
open Formalism.FourierDecayAlt.P.C2x6
open C2x5
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.C2x6.herm_ff {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (a b : Fin (r + 1)) :
    herm (Hpk k r) (fvec k r z b) (fvec k r z a) = C2.Adiag k r z a b := by sorry
