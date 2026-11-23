-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_isN_red
-- name    : Formalism.FourierDecayAlt.P.S3x2.isN_red
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:07.413434+00:00
-- url     : https://prove2.me/theorems/f079fae1-d971-4914-b8fe-e391643ab63e
-- title:
--   S3x2: is N red
-- statement:
--   The S3x2 construction uses the is N red property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReductionSurjective.lean#L405-L407
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReductionSurjective.lean#L405-L407

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x2
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.S3
variable (o : Type) [CommRing o] [IsLocalRing o]
local notation "𝔽" => IsLocalRing.ResidueField o
variable {o} {r k : ℕ}

theorem Formalism.FourierDecayAlt.P.S3x2.isN_red {n : GL (Idx r k) o} (hn : IsN (n : Matrix (Idx r k) (Idx r k) o)) :
    IsN (red o (Idx r k) n : Matrix (Idx r k) (Idx r k) 𝔽) := by sorry
