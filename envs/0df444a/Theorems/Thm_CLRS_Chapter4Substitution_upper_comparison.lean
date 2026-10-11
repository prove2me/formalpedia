-- Prove2me | Theorems.Thm_CLRS_Chapter4Substitution_upper_comparison
-- name    : CLRS.Chapter4Substitution.upper_comparison
-- status  : Proved
-- author  : @Chutong
-- created : 2026-10-11T05:08:03.935556+00:00
-- url     : https://prove2.me/theorems/78abcbf9-c42f-4403-b9f5-9bd8e63750ff
-- title:
--   CLRS §4.3: general upper substitution for smaller recursive children
-- statement:
--   Let $\operatorname{children}(n)$ be a finite ordered list
--   of natural child sizes, let $g:\mathbb N\to\mathbb N$ be the local toll,
--   and let $b$ be a natural cutoff. At every $n\ge b$, assume each listed
--   child is strictly smaller than $n$. Repeated children count with multiplicity.
--
--   Let $T,B:\mathbb N\to\mathbb N$ be a cost and candidate bound. Assume
--   $T(n)\le B(n)$ at every base size $n<b$ and, for every $n\ge b$,
--
--   $$T(n)\le g(n)+\sum_m T(m),\qquad g(n)+\sum_m B(m)\le B(n),$$
--
--   where both sums range over the listed children of $n$. Then $T(n)\le B(n)$
--   at every natural size. Unequal splits, empty child lists, and zero costs are
--   permitted. This is a reusable numerical comparison principle; it does not
--   assume an algorithm execution or a specific asymptotic form.
--
--   **Platform namespace.** The imported Chapter 4 source declarations live under `CLRS` in this upload to avoid collisions with independently published compiler versions. The immutable source reference retains the original declaration names.
-- source:
--   Algo2Lean Chapter 4 development, declaration Chapter4Substitution.upper_comparison, immutable source fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41: https://github.com/chutongyang98/Lean_formalization/blob/fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41/proofs/chapter4/Substitution.lean#L77-L96

import Definitions.Def_CLRS_Chapter4_Substitution
import Std

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CLRS
end CLRS
open CLRS
namespace CLRS.Chapter4Substitution
end CLRS.Chapter4Substitution
open CLRS.Chapter4Substitution

theorem CLRS.Chapter4Substitution.upper_comparison (children : Nat → List Nat) (toll : Nat → Nat)
    (cutoff : Nat) (cost candidate : Nat → Nat)
    (smaller : SmallerChildren children cutoff)
    (base : ∀ n, n < cutoff → cost n ≤ candidate n)
    (recurrence : UpperRecurrence children toll cutoff cost)
    (substitution : UpperCandidate children toll cutoff candidate) :
    ∀ n, cost n ≤ candidate n := by sorry
