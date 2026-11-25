-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_ge_cauchyBinet
-- name    : Formalism.HermitianLatticeCounting.P.ge_cauchyBinet
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:29:58.19631+00:00
-- url     : https://prove2.me/theorems/1ef7acbc-7074-5108-8bd7-c94e6a3957e3
-- title:
--   P: ge cauchy Binet
-- statement:
--   The P construction uses the ge cauchy Binet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L767-L773
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L767-L773

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
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset Matrix Polynomial
open scoped ComplexConjugate

theorem Formalism.HermitianLatticeCounting.P.ge_cauchyBinet {K : Type*} [CommRing K] {i n : ℕ} (A : Matrix (Fin i) (Fin n) K)
    (B : Matrix (Fin n) (Fin i) K) :
    (A * B).det = ∑ I : {I : Finset (Fin n) // I.card = i},
      (B.submatrix (I.1.orderEmbOfFin I.2) id).det * (A.submatrix id (I.1.orderEmbOfFin I.2)).det := by sorry
