-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_gh_det_upper
-- name    : Formalism.HermitianLatticeCounting.P.gh_det_upper
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:03:37.839978+00:00
-- url     : https://prove2.me/theorems/ea2a1ec4-7e2c-4370-a204-7a5f6973a49e
-- title:
--   P: gh det upper
-- statement:
--   The P construction uses the gh det upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L523-L526
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L523-L526

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
variable {n β K : Type*} [Fintype n] [DecidableEq n] [LinearOrder n] [LinearOrder β] [Field K]
  {b : n → β} {σ : n → n}
omit [LinearOrder β]

theorem Formalism.HermitianLatticeCounting.P.gh_det_upper {u : Matrix n n K} (h1 : ∀ i, u i i = 1) (h2 : ∀ i j, j < i → u i j = 0) :
    u.det = 1 := by sorry
