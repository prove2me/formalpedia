-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_gi_lead_eq
-- name    : Formalism.HermitianLatticeCounting.P.gi_lead_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:31.659998+00:00
-- url     : https://prove2.me/theorems/350a1ac8-bff8-4286-be26-bc0b9f91895c
-- title:
--   P: gi lead eq
-- statement:
--   The P construction uses the gi lead eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L549-L557
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L549-L557

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
open scoped ComplexConjugate

theorem Formalism.HermitianLatticeCounting.P.gi_lead_eq {R : Type*} [CommRing R] (r : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R) :
    leadingPrincipalMinor Z r = (Z.submatrix Fin.castSucc Fin.castSucc).det := by sorry
