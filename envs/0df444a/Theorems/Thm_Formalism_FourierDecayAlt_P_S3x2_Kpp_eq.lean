-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_Kpp_eq
-- name    : Formalism.FourierDecayAlt.P.S3x2.Kpp_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:20.932698+00:00
-- url     : https://prove2.me/theorems/32a5a5f5-3469-433d-8a32-8b457e1897de
-- title:
--   S3x2: Kpp eq
-- statement:
--   The S3x2 construction uses the Kpp eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReductionSurjective.lean#L409-L411
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReductionSurjective.lean#L409-L411

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

theorem Formalism.FourierDecayAlt.P.S3x2.Kpp_eq (L : Levels o r k) : L.Kpp = (PG r (upUniG 𝔽 k)).comap (red o (Idx r k)) := by sorry
