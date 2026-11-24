-- Prove2me | Theorems.Thm_Formalism_L2_Pj_CompSplitPfC_cspC_idem_of
-- name    : Formalism.L2.Pj.CompSplitPfC.cspC_idem_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:48.754795+00:00
-- url     : https://prove2.me/theorems/4f2744e7-7d33-4357-851f-825155f86241
-- title:
--   Comp Split Pf C: csp C idem of
-- statement:
--   The Comp Split Pf C construction uses the csp C idem of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompSplitPfC.lean#L50-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompSplitPfC.lean#L50-L59

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompSplitPfC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.CompSplitPfC
open TensorProduct
variable {P S : Type} [CommRing P] [IsDomain P] [IsIntegrallyClosed P] [CommRing S] [Algebra P S]
  [Algebra.Etale P S]

theorem Formalism.L2.Pj.CompSplitPfC.cspC_idem_of {r : S ⊗[P] FractionRing P} (hr : IsIdempotentElem r) :
    ∃ s : S, algebraMap S (S ⊗[P] FractionRing P) s = r := by sorry
