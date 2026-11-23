-- Prove2me | Theorems.Thm_Formalism_L2_Pj_CompSplitPfC_cspC_alg
-- name    : Formalism.L2.Pj.CompSplitPfC.cspC_alg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:41:23.820304+00:00
-- url     : https://prove2.me/theorems/ed085692-c1bb-499a-8e0a-97e19ce2bbc5
-- title:
--   Comp Split Pf C: csp C alg
-- statement:
--   The Comp Split Pf C construction uses the csp C alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompSplitPfC.lean#L12-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompSplitPfC.lean#L12-L12

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

theorem Formalism.L2.Pj.CompSplitPfC.cspC_alg (s : S) : algebraMap S (S ⊗[P] FractionRing P) s = s ⊗ₜ (1 : FractionRing P) := by sorry
