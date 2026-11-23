-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G4_tri_mul
-- name    : Formalism.FourierDecayAlt.P.G4.tri_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:33.791805+00:00
-- url     : https://prove2.me/theorems/2239ca2d-ec56-4544-b6e0-87254f0dd043
-- title:
--   G4: tri mul
-- statement:
--   The G4 construction uses the tri mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L151-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L151-L157

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.FourierDecayAlt.G
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G4

theorem Formalism.FourierDecayAlt.P.G4.tri_mul {d : ℕ} {p q : Matrix (Fin d) (Fin d) ℂ} (hp : ∀ i j, j < i → p i j = 0)
    (hq : ∀ i j, j < i → q i j = 0) (i j : Fin d) (hij : j < i) : (p * q) i j = 0 := by sorry
