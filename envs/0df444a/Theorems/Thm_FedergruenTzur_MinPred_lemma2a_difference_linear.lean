-- Prove2me | Theorems.Thm_FedergruenTzur_MinPred_lemma2a_difference_linear
-- name    : FedergruenTzur.MinPred.lemma2a_difference_linear
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:54:24.740732+00:00
-- url     : https://prove2.me/theorems/a5d743de-eeee-4af3-9486-5942db8039f7
-- title:
--   LEMMA 2(a): Δ_{k,l}(t) = A(k, l) + (c_{k,l} − c_l)D(t), a linear function of D(t) with t-independent coefficients
-- statement:
--   In the dynamic lot size model with costs given by the recursion (2), fix periods $1 \le k < l$. Then for every horizon $t \ge l$ the difference of the costs with last setup in $k$ and in $l$ is
--   $$
--   \Delta_{k,l}(t) = F(k, t) - F(l, t) = A(k, l) + (c_{k,l} - c_l)\,D(t),
--   $$
--   with $A(k,l)$ the intercept (4). The same identity holds for the potential costs: for every $j \ge l$ and every potential cumulative demand $x \in \mathbb R$,
--   $$
--   \pi_j(k, x) - \pi_j(l, x) = A(k, l) + (c_{k,l} - c_l)\,x.
--   $$
--
--   Thus $\Delta_{k,l}$ is an affine function of the cumulative demand whose coefficients do not depend on the horizon. This is the basic fact behind the forward algorithm: which of two periods is the better last setup period is decided by comparing the cumulative demand with a single root.
--
--   **Formalization Note.** The second conjunct, at an arbitrary real potential cumulative demand, is the form in which the paper uses Lemma 2 in the proof of Theorem 1 ("for all horizons $t$ with $D(t) \ge \dots$"); by the encoding certificate `potCost_spec` it is the first conjunct with $D(t)$ replaced by a free parameter.
-- source:
--   Federgruen and Tzur, A Simple Forward Algorithm to Solve General Dynamic Lot Sizing Models with n Periods in O(n log n) or O(n) Time, Management Science 37(8), 1991, p. 914, LEMMA 2(a) (derivation on p. 913)

import Mathlib
import Definitions.Def_FedergruenTzur_MinPred_Breakpoint
import Definitions.Def_FedergruenTzur_MinPred_Omega

namespace FedergruenTzur.MinPred

open LotSizing

/-- LEMMA 2(a), p. 914: for periods `k < l ≤ t`,
`Δ_{k,l}(t) = F(k, t) - F(l, t) = A(k, l) + (c_{k,l} - c_l) D(t)`.
The second conjunct is the same identity for the potential costs at an arbitrary potential cumulative
demand `x` (horizons beyond `j ≥ l`), the form used in the proof of Theorem 1 (Appendix, p. 923). -/
theorem lemma2a_difference_linear (P : LotSizing) (k l : ℕ) (hk : 1 ≤ k) (hkl : k < l) :
    (∀ t, l ≤ t → P.Flast k t - P.Flast l t = P.A k l + (P.cij k l - P.c l) * P.D t) ∧
    (∀ j, l ≤ j → ∀ x : ℝ,
      P.potCost j k x - P.potCost j l x = P.A k l + (P.cij k l - P.c l) * x) := by sorry

end FedergruenTzur.MinPred
