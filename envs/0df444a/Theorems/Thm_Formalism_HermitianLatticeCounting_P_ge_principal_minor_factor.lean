-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_ge_principal_minor_factor
-- name    : Formalism.HermitianLatticeCounting.P.ge_principal_minor_factor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:27.775321+00:00
-- url     : https://prove2.me/theorems/99c2d7fa-e519-403f-b835-18b4b464aabc
-- title:
--   P: ge principal minor factor
-- statement:
--   The P construction uses the ge principal minor factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L760-L765
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L760-L765

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

theorem Formalism.HermitianLatticeCounting.P.ge_principal_minor_factor {K : Type*} [CommRing K] {i n : ℕ} (A : Matrix (Fin i) (Fin n) K)
    (B : Matrix (Fin n) (Fin i) K) (S : Finset (Fin n)) (hS : S.card = i) :
    ((B * A).submatrix (Subtype.val : S → Fin n) Subtype.val).det
      = (B.submatrix (S.orderEmbOfFin hS) id).det * (A.submatrix id (S.orderEmbOfFin hS)).det := by sorry
