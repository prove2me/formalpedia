-- Prove2me | Theorems.Thm_CLRS_Chapter4Substitution_lower_comparison
-- name    : CLRS.Chapter4Substitution.lower_comparison
-- status  : Proved
-- author  : @Chutong
-- created : 2026-10-11T05:08:08.946032+00:00
-- url     : https://prove2.me/theorems/39a37a4e-158f-43ea-aa77-7a24c2725cae
-- title:
--   CLRS §4.3: general lower substitution for smaller recursive children
-- statement:
--   Let $\operatorname{children}(n)$ be a finite ordered list
--   of natural child sizes, let $g:\mathbb N\to\mathbb N$ be the local toll,
--   and let $b$ be a natural cutoff. At every $n\ge b$, assume each listed
--   child is strictly smaller than $n$. Repeated children count with multiplicity.
--
--   Let $T,B:\mathbb N\to\mathbb N$ be a cost and candidate bound. Assume
--   $B(n)\le T(n)$ at every base size $n<b$ and, for every $n\ge b$,
--
--   $$g(n)+\sum_m T(m)\le T(n),\qquad B(n)\le g(n)+\sum_m B(m),$$
--
--   where both sums range over the listed children of $n$. Then $B(n)\le T(n)$
--   at every natural size. Unequal splits, empty child lists, and zero costs are
--   permitted. This is a reusable numerical comparison principle; it does not
--   assume an algorithm execution or a specific asymptotic form.
--
--   **Platform namespace.** The imported Chapter 4 source declarations live under `CLRS` in this upload to avoid collisions with independently published compiler versions. The immutable source reference retains the original declaration names.
-- source:
--   Algo2Lean Chapter 4 development, declaration Chapter4Substitution.lower_comparison, immutable source fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41: https://github.com/chutongyang98/Lean_formalization/blob/fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41/proofs/chapter4/Substitution.lean#L98-L117

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

theorem CLRS.Chapter4Substitution.lower_comparison (children : Nat → List Nat) (toll : Nat → Nat)
    (cutoff : Nat) (cost candidate : Nat → Nat)
    (smaller : SmallerChildren children cutoff)
    (base : ∀ n, n < cutoff → candidate n ≤ cost n)
    (recurrence : LowerRecurrence children toll cutoff cost)
    (substitution : LowerCandidate children toll cutoff candidate) :
    ∀ n, candidate n ≤ cost n := by sorry
