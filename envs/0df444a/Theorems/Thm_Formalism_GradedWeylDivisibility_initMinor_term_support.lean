-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_initMinor_term_support
-- name    : Formalism.GradedWeylDivisibility.initMinor_term_support
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:58:37.330803+00:00
-- url     : https://prove2.me/theorems/661a1865-c36d-4902-8fde-4e81c47e25ac
-- title:
--   Graded Weyl Divisibility: init Minor term support
-- statement:
--   The Graded Weyl Divisibility construction uses the init Minor term support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetdomLemmas.lean#L102-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetdomLemmas.lean#L102-L129

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

theorem Formalism.GradedWeylDivisibility.initMinor_term_support {R : Type*} [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n)
    (σ : Equiv.Perm (Fin s)) (m : Fin r × Fin n →₀ ℕ)
    (hm : m ∈ (∏ i : Fin s, (X (I (σ i), Fin.castLE hs i) : MvPolynomial (Fin r × Fin n) R)).support) :
    (∀ k, rowPart k m = #{p : Fin s | (I p).val < k}) ∧ rowTot m = s := by sorry
