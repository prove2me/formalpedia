-- Prove2me | Theorems.Thm_CLRS_Chapter4RecursionTree_recurrence_tree_accounting
-- name    : CLRS.Chapter4RecursionTree.recurrence_tree_accounting
-- status  : Proved
-- author  : @Chutong
-- created : 2026-10-11T05:08:10.904214+00:00
-- url     : https://prove2.me/theorems/e0a3605c-8eae-480d-accc-5b6c8a0bf482
-- title:
--   CLRS §4.4: exact recurrence cost is the work on a finite tree
-- statement:
--   Fix a finite ordered child-size list at every natural size,
--   natural-valued toll and base-work functions, and a natural cutoff. A tree
--   is consistent when sizes below the cutoff are leaves with their base work,
--   and every other node has its toll as local work and the prescribed ordered
--   list of child root sizes.
--
--   Assume every non-base child is strictly smaller than its parent. Let a
--   natural-valued function $T$ match the base work and the exact toll-plus-child
--   recurrence. For every natural input $n$, there is a finite consistent tree
--   $\tau$ rooted at $n$ for which
--
--   $$T(n)=\operatorname{totalCost}(\tau)
--   =\sum_{\ell=0}^{\operatorname{height}(\tau)-1}
--   \operatorname{levelCost}(\tau,\ell).$$
--
--   This unites tree existence and exact accounting without balance assumptions.
--   It applies to a numerical recurrence; a source-program runtime claim must
--   separately identify its completed execution's cost with that recurrence.
--
--   **Platform namespace.** The imported Chapter 4 source declarations live under `CLRS` in this upload to avoid collisions with independently published compiler versions. The immutable source reference retains the original declaration names.
-- source:
--   Algo2Lean Chapter 4 development, declaration Chapter4RecursionTree.recurrence_tree_accounting, immutable source fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41: https://github.com/chutongyang98/Lean_formalization/blob/fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41/proofs/chapter4/RecursionTree.lean#L267-L277

import Definitions.Def_CLRS_Chapter4_RecursionTree
import Definitions.Def_CLRS_Chapter4_Substitution
import Std

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CLRS
end CLRS
open CLRS
namespace CLRS.Chapter4RecursionTree
end CLRS.Chapter4RecursionTree
open CLRS.Chapter4RecursionTree

theorem CLRS.Chapter4RecursionTree.recurrence_tree_accounting (children : Nat → List Nat) (toll base : Nat → Nat) (cutoff : Nat)
    (cost : Nat → Nat) (smaller : Chapter4Substitution.SmallerChildren children cutoff)
    (baseCost : ∀ n, n < cutoff → cost n = base n)
    (recurrence : Chapter4Substitution.ExactRecurrence children toll cutoff cost) (size : Nat) :
    ∃ tree, tree.rootSize = size ∧ Consistent children toll base cutoff tree ∧
      cost size = tree.totalCost ∧ cost size = sumBelow tree.height tree.levelCost := by sorry
