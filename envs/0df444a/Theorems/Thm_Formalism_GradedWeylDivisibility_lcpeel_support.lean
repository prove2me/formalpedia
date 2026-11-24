-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lcpeel_support
-- name    : Formalism.GradedWeylDivisibility.lcpeel_support
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:12.456798+00:00
-- url     : https://prove2.me/theorems/84ed37fd-5708-4895-b396-7f7876a6452f
-- title:
--   Graded Weyl Divisibility: lcpeel support
-- statement:
--   The Graded Weyl Divisibility construction uses the lcpeel support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/PeelHomog.lean#L9-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/PeelHomog.lean#L9-L21

import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCpeelLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_PeelHomog
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.lcpeel_support {B : Type*} [CommRing B] {r n : ℕ} (l j : Fin n) (a0 : Fin r) (k : ℕ)
    (g : MvPolynomial (Fin r × Fin n) B) (d : Fin r × Fin n →₀ ℕ)
    (hd : coeff d (peel l j a0 k g) ≠ 0) :
    ∃ m ∈ g.support, m (a0, l) = k ∧ d = (m.erase (a0, l)).erase (a0, j) := by sorry
