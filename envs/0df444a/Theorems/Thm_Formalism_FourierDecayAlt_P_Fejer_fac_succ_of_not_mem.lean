-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fejer_fac_succ_of_not_mem
-- name    : Formalism.FourierDecayAlt.P.Fejer.fac_succ_of_not_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:11.871043+00:00
-- url     : https://prove2.me/theorems/04e8dc94-cb8d-41bd-9deb-9f3f4ca94930
-- title:
--   Fejer: fac succ of not mem
-- statement:
--   The Fejer construction uses the fac succ of not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FacSuccOfNotMem.lean#L23-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FacSuccOfNotMem.lean#L23-L32

import Definitions.Def_Formalism_HermitianCurvature_StatementH
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FacSuccOfNotMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fejer
open Real Finset Formalism.FourierDecayAlt.P.Herglotz
variable {d : ℕ}

theorem Formalism.FourierDecayAlt.P.Fejer.fac_succ_of_not_mem (N : ℕ) (t : ℤ) (ht : t ∉ Finset.Icc (-(N : ℤ)) N) :
    fac (N + 1) t = 0 := by sorry
