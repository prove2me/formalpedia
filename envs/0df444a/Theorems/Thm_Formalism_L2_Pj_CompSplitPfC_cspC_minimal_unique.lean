-- Prove2me | Theorems.Thm_Formalism_L2_Pj_CompSplitPfC_cspC_minimal_unique
-- name    : Formalism.L2.Pj.CompSplitPfC.cspC_minimal_unique
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:56.044665+00:00
-- url     : https://prove2.me/theorems/5d441df3-9c66-4eca-b8e7-967a0f992bae
-- title:
--   Comp Split Pf C: csp C minimal unique
-- statement:
--   The Comp Split Pf C construction uses the csp C minimal unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompSplitPfC.lean#L63-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompSplitPfC.lean#L63-L103

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
variable (P)
include P

theorem Formalism.L2.Pj.CompSplitPfC.cspC_minimal_unique {q P1 P2 : Ideal S} [hq : q.IsPrime] (h1 : P1 ∈ minimalPrimes S)
    (h2 : P2 ∈ minimalPrimes S) (hq1 : P1 ≤ q) (hq2 : P2 ≤ q) : P1 = P2 := by sorry
