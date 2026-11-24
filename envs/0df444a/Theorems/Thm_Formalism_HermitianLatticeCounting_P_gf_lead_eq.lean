-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_gf_lead_eq
-- name    : Formalism.HermitianLatticeCounting.P.gf_lead_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:35.013304+00:00
-- url     : https://prove2.me/theorems/65178a11-0dd2-4618-85d0-bf48436886aa
-- title:
--   P: gf lead eq
-- statement:
--   The P construction uses the gf lead eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L366-L374
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L366-L374

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

theorem Formalism.HermitianLatticeCounting.P.gf_lead_eq {R : Type*} [CommRing R] {d : ℕ} (Z : Matrix (Fin d) (Fin d) R) (q : ℕ) (h : q ≤ d) :
    leadingPrincipalMinor Z q = (Z.submatrix (Fin.castLE h) (Fin.castLE h)).det := by sorry
