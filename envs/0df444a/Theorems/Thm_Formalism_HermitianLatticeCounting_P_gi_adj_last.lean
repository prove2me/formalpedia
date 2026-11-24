-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_gi_adj_last
-- name    : Formalism.HermitianLatticeCounting.P.gi_adj_last
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:29.950218+00:00
-- url     : https://prove2.me/theorems/04e5f179-5e12-4d42-80db-ce64fe786679
-- title:
--   P: gi adj last
-- statement:
--   The P construction uses the gi adj last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L559-L562
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L559-L562

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

theorem Formalism.HermitianLatticeCounting.P.gi_adj_last {R : Type*} [CommRing R] (r : ℕ) (M : Matrix (Fin (r + 1)) (Fin (r + 1)) R) :
    M.adjugate (Fin.last r) (Fin.last r) = leadingPrincipalMinor M r := by sorry
