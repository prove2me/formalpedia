-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_gc_inner
-- name    : Formalism.HermitianLatticeCounting.P.gc_inner
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:21.261513+00:00
-- url     : https://prove2.me/theorems/c5c2b361-cf4e-4231-b797-141a0c81b17f
-- title:
--   P: gc inner
-- statement:
--   The P construction uses the gc inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L922-L936
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L922-L936

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

theorem Formalism.HermitianLatticeCounting.P.gc_inner {l : ℕ} (y : Fin l → V) (a b : Fin l) :
    inner ℂ (y a) (y b) =
      ∑ c, conj (gramSchmidtUnitriangularMatrix y a c) * ((‖gramSchmidt ℂ y c‖ : ℂ) ^ 2) * gramSchmidtUnitriangularMatrix y b c := by sorry
