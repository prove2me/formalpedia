-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_gf_one_lower
-- name    : Formalism.HermitianLatticeCounting.P.gf_one_lower
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:34.159137+00:00
-- url     : https://prove2.me/theorems/b8abfd53-3c99-48b0-bce5-5bbaa7d589bb
-- title:
--   P: gf one lower
-- statement:
--   The P construction uses the gf one lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L376-L378
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L376-L378

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset Matrix

theorem Formalism.HermitianLatticeCounting.P.gf_one_lower {R : Type*} [CommRing R] {d : ℕ} : IsLowerUnitriangular (1 : Matrix (Fin d) (Fin d) R) := by sorry
