-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_gg_index_eq
-- name    : Formalism.HermitianLatticeCounting.P.gg_index_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:29:33.666716+00:00
-- url     : https://prove2.me/theorems/64dd420d-626f-468e-832b-41a15978b21c
-- title:
--   P: gg index eq
-- statement:
--   The P construction uses the gg index eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L158-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L158-L165

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

theorem Formalism.HermitianLatticeCounting.P.gg_index_eq {d : ℕ} (c : Composition d) (i : Fin d) (a : ℕ)
    (h1 : c.sizeUpTo a ≤ (i : ℕ)) (h2 : (i : ℕ) < c.sizeUpTo (a + 1)) : (c.index i : ℕ) = a := by sorry
