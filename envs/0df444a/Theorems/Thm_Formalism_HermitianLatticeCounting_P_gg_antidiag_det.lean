-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_gg_antidiag_det
-- name    : Formalism.HermitianLatticeCounting.P.gg_antidiag_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:25.275681+00:00
-- url     : https://prove2.me/theorems/183cb05a-5366-4a25-80de-463576055c00
-- title:
--   P: gg antidiag det
-- statement:
--   The P construction uses the gg antidiag det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L167-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L167-L197

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

theorem Formalism.HermitianLatticeCounting.P.gg_antidiag_det {R : Type*} [CommRing R] (t : R) (s : ℕ) :
    (Matrix.of fun i j : Fin s => if (i : ℕ) + (j : ℕ) + 1 = s then t else 0).det =
      (-1) ^ (s.choose 2) * t ^ s := by sorry
