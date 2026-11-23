-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_lin
-- name    : Formalism.BranchingDeterminantCap.bmK_lin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:24:31.112491+00:00
-- url     : https://prove2.me/theorems/07f691d8-8d2f-4dc0-8c9d-9395ea8a79c0
-- title:
--   Branching Determinant Cap: bm K lin
-- statement:
--   The Branching Determinant Cap construction uses the bm K lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2575-L2590
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2575-L2590

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap

theorem Formalism.BranchingDeterminantCap.bmK_lin {R M N P : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (rel : M → N → Prop) (Z : N →ₗ[R] P) (hex : ∀ f, ∃ G, rel f G)
    (hadd : ∀ f f' G G', rel f G → rel f' G' → rel (f + f') (G + G'))
    (hsmul : ∀ (c : R) f G, rel f G → rel (c • f) (c • G))
    (hkey : ∀ f G G', rel f G → rel f G' → Z G = Z G') :
    ∃ io : M →ₗ[R] P, ∀ f G, rel f G → io f = Z G := by sorry
