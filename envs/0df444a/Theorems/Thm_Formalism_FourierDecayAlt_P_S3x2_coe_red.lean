-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_coe_red
-- name    : Formalism.FourierDecayAlt.P.S3x2.coe_red
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:13.216936+00:00
-- url     : https://prove2.me/theorems/7c08840c-5d6f-4503-97fc-49f70bf56b31
-- title:
--   S3x2: coe red
-- statement:
--   The S3x2 construction uses the coe red property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReductionSurjective.lean#L357-L358
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReductionSurjective.lean#L357-L358

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

theorem Formalism.FourierDecayAlt.P.S3x2.coe_red (ι : Type) [Fintype ι] [DecidableEq ι] (g : GL ι o) :
    (red o ι g : Matrix ι ι 𝔽) = (g : Matrix ι ι o).map (IsLocalRing.residue o) := by sorry
