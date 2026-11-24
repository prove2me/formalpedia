-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_gj_fvec_apply
-- name    : Formalism.HermitianLatticeCounting.P.gj_fvec_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:37:18.512567+00:00
-- url     : https://prove2.me/theorems/82af45a6-41f5-4473-8222-1240dd5c43e3
-- title:
--   P: gj fvec apply
-- statement:
--   The P construction uses the gj fvec apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L675-L677
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L675-L677

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
open Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts Matrix Finset

theorem Formalism.HermitianLatticeCounting.P.gj_fvec_apply (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin (r + 1)) (hc : c.val < r)
    (i : Fin (2 * r + k + 1)) : fvec k r z c i = if i.val = c.val then 1 else 0 := by sorry
