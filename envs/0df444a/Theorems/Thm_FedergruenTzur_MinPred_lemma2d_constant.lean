-- Prove2me | Theorems.Thm_FedergruenTzur_MinPred_lemma2d_constant
-- name    : FedergruenTzur.MinPred.lemma2d_constant
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:53:21.628045+00:00
-- url     : https://prove2.me/theorems/2d48f621-8cfb-402c-9135-f7b80a64abf6
-- title:
--   LEMMA 2(d), corrected: if c_{k,l} = c_l then Δ_{k,l} is constant and, for A(k, l) ≠ 0, Δ_{k,l} ≥ 0 iff D(t) ≥ G(k, l)
-- statement:
--   In the dynamic lot size model, fix periods $1 \le k < l$ and write the difference function of Lemma 2(a) as $\Delta_{k,l}(D) = A(k,l) + (c_{k,l} - c_l)\,D$. If $c_{k,l} = c_l$, then $\Delta_{k,l}$ is constant, equal to $A(k,l)$, and, provided $A(k,l) \ne 0$, for every $D \in \mathbb R$
--   $$
--   \Delta_{k,l}(D) \ge 0 \iff D \ge G(k, l).
--   $$
--
--   When the two slopes agree, one of the two periods dominates the other for every cumulative demand; the convention $G = \pm\infty$ of (5) encodes which one.
--
--   **Formalization Note.** Two corrections of the printed text are made. (1) The page prints the hypothesis as "$c_{k,l} < c_l$", which repeats part (c) and cannot yield a constant function; the constant case is $c_{k,l} = c_l$, i.e. $\tilde C(k) = \tilde C(l)$, the infinite cases of (5). (2) When $A(k,l) = 0$, (5) gives $G(k,l) = +\infty$, so "$D \ge G(k,l)$" is false while $\Delta_{k,l} = 0 \ge 0$; the equivalence is therefore stated under $A(k,l) \ne 0$. Both cases are otherwise as printed.
-- source:
--   Federgruen and Tzur, A Simple Forward Algorithm to Solve General Dynamic Lot Sizing Models with n Periods in O(n log n) or O(n) Time, Management Science 37(8), 1991, p. 914, LEMMA 2(d) (printed hypothesis 'c_{k,l} < c_l' corrected to '=', see Formalization Note)

import Mathlib
import Definitions.Def_FedergruenTzur_MinPred_Breakpoint

namespace FedergruenTzur.MinPred

open LotSizing

/-- LEMMA 2(d), p. 914, corrected: for periods `k < l`, if `c_{k,l} = c_l` (printed: `<`) then the
difference function `D ↦ A(k, l) + (c_{k,l} - c_l) D` is constant, and, when `A(k, l) ≠ 0`, it is
`≥ 0` if and only if `D ≥ G(k, l)`. (At `A(k, l) = 0`, (5) gives `G(k, l) = +∞` while `Δ_{k,l} = 0`.) -/
theorem lemma2d_constant (P : LotSizing) (k l : ℕ) (hk : 1 ≤ k) (hkl : k < l)
    (hc : P.cij k l = P.c l) :
    (∀ x : ℝ, P.A k l + (P.cij k l - P.c l) * x = P.A k l) ∧
    (P.A k l ≠ 0 →
      ∀ x : ℝ, (0 ≤ P.A k l + (P.cij k l - P.c l) * x ↔ P.G k l ≤ (x : EReal))) := by sorry

end FedergruenTzur.MinPred
