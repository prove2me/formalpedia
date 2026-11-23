-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_gf_lower_det
-- name    : Formalism.HermitianLatticeCounting.P.gf_lower_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:03:06.255412+00:00
-- url     : https://prove2.me/theorems/e7346f2f-4685-4f6e-a5f1-89ed6f21e9b5
-- title:
--   P: gf lower det
-- statement:
--   The P construction uses the gf lower det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L341-L346
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L341-L346

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

theorem Formalism.HermitianLatticeCounting.P.gf_lower_det {R : Type*} [CommRing R] {d : ℕ} {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (ρ : α → Fin d) (hmono : StrictMono ρ) (l : Matrix (Fin d) (Fin d) R) (hl : IsLowerUnitriangular l) :
    (l.submatrix ρ ρ).det = 1 := by sorry
