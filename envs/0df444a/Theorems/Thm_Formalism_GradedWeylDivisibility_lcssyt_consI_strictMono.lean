-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lcssyt_consI_strictMono
-- name    : Formalism.GradedWeylDivisibility.lcssyt_consI_strictMono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:34.776057+00:00
-- url     : https://prove2.me/theorems/cccc3581-abcf-48f8-a7dc-dd7fd41a8977
-- title:
--   Graded Weyl Divisibility: lcssyt cons I strict Mono
-- statement:
--   The Graded Weyl Divisibility construction uses the lcssyt cons I strict Mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LCssytLemmas.lean#L98-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LCssytLemmas.lean#L98-L103

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCssytLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.lcssyt_consI_strictMono {r K h : ℕ} (sz : Fin K → ℕ) (c : Fin h → Fin r) (I : ∀ k, Fin (sz k) → Fin r)
    (hc : StrictMono c) (hI : ∀ k, StrictMono (I k)) : ∀ k, StrictMono (lcssyt_consI sz c I k) := by sorry
