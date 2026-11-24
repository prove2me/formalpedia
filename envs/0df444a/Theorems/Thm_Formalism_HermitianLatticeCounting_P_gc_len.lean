-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_gc_len
-- name    : Formalism.HermitianLatticeCounting.P.gc_len
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:26.780804+00:00
-- url     : https://prove2.me/theorems/2a539fe2-dd35-4ba9-96fa-6761190aca48
-- title:
--   P: gc len
-- statement:
--   The P construction uses the gc len property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L961-L990
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L961-L990

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
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset Matrix InnerProductSpace
open scoped ComplexConjugate
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem Formalism.HermitianLatticeCounting.P.gc_len {l : ℕ} (y : Fin l → V) (a : Fin l) :
    majorantDistance y a = ‖gramSchmidt ℂ y a‖ := by sorry
