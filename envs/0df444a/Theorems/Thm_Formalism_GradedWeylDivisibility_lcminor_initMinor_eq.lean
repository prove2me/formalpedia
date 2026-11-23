-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lcminor_initMinor_eq
-- name    : Formalism.GradedWeylDivisibility.lcminor_initMinor_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:52:18.177116+00:00
-- url     : https://prove2.me/theorems/63d1173f-3327-4403-810e-124c8fcd14e5
-- title:
--   Graded Weyl Divisibility: lcminor init Minor eq
-- statement:
--   The Graded Weyl Divisibility construction uses the lcminor init Minor eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/ColLexInitMinor.lean#L11-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/ColLexInitMinor.lean#L11-L20

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ColLexInitMinor
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
open scoped MonomialOrder

theorem Formalism.GradedWeylDivisibility.lcminor_initMinor_eq (R : Type) [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n) :
    initMinor R I hs = ∑ σ : Equiv.Perm (Fin s),
      monomial (∑ q : Fin s, Finsupp.single (I (σ q), Fin.castLE hs q) 1)
        (((Equiv.Perm.sign σ : ℤ) : R)) := by sorry
