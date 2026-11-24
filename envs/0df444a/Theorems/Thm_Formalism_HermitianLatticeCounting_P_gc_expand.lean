-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_gc_expand
-- name    : Formalism.HermitianLatticeCounting.P.gc_expand
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:25.447249+00:00
-- url     : https://prove2.me/theorems/edc8fe22-b529-4800-8624-c0711fa0cd69
-- title:
--   P: gc expand
-- statement:
--   The P construction uses the gc expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L903-L920
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L903-L920

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

theorem Formalism.HermitianLatticeCounting.P.gc_expand {l : ℕ} (y : Fin l → V) (a : Fin l) :
    y a = ∑ b, gramSchmidtUnitriangularMatrix y a b • gramSchmidt ℂ y b := by sorry
