-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_initMinor_support
-- name    : Formalism.GradedWeylDivisibility.initMinor_support
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:22:33.512413+00:00
-- url     : https://prove2.me/theorems/9b28fbc0-9cc3-4db2-bd74-b672dbb3403c
-- title:
--   Graded Weyl Divisibility: init Minor support
-- statement:
--   The Graded Weyl Divisibility construction uses the init Minor support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetdomLemmas.lean#L131-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetdomLemmas.lean#L131-L167

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetdomLemmas
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

theorem Formalism.GradedWeylDivisibility.initMinor_support {R : Type*} [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n)
    (m : Fin r × Fin n →₀ ℕ) (hm : m ∈ (initMinor R I hs).support) :
    (∀ k, rowPart k m ≤ min k s) ∧ rowTot m = s := by sorry
