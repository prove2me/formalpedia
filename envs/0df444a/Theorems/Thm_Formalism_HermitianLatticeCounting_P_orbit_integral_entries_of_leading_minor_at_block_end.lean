-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_orbit_integral_entries_of_leading_minor_at_block_end
-- name    : Formalism.HermitianLatticeCounting.P.orbit_integral_entries_of_leading_minor_at_block_end
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:36.374799+00:00
-- url     : https://prove2.me/theorems/347b5e85-1cfb-43e0-a866-d769145cf0c3
-- title:
--   P: orbit integral entries of leading minor at block end
-- statement:
--   The P construction uses the orbit integral entries of leading minor at block end property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L477-L506
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L477-L506

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

theorem Formalism.HermitianLatticeCounting.P.orbit_integral_entries_of_leading_minor_at_block_end (hV : Formalism.HermitianLatticeCounting.ExpansionTerms.LeadingMinorAtBlockEnd) : Formalism.HermitianLatticeCounting.ExpansionTerms.OrbitIntegralEntries := by sorry
