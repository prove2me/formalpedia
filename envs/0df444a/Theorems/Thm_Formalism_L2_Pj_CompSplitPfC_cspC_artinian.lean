-- Prove2me | Theorems.Thm_Formalism_L2_Pj_CompSplitPfC_cspC_artinian
-- name    : Formalism.L2.Pj.CompSplitPfC.cspC_artinian
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:01.318468+00:00
-- url     : https://prove2.me/theorems/f0c94c71-0189-483a-b151-63a435c6250f
-- title:
--   Comp Split Pf C: csp C artinian
-- statement:
--   The Comp Split Pf C construction uses the csp C artinian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompSplitPfC.lean#L27-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompSplitPfC.lean#L27-L33

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

theorem Formalism.L2.Pj.CompSplitPfC.cspC_artinian : IsArtinianRing (S ⊗[P] FractionRing P) := by sorry
