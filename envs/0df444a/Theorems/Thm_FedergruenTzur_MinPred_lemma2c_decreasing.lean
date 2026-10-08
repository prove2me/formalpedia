-- Prove2me | Theorems.Thm_FedergruenTzur_MinPred_lemma2c_decreasing
-- name    : FedergruenTzur.MinPred.lemma2c_decreasing
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:53:27.808884+00:00
-- url     : https://prove2.me/theorems/e3787c54-8ac0-454f-af82-eb58de401e9f
-- title:
--   LEMMA 2(c): if c_{k,l} < c_l then Δ_{k,l} is decreasing and Δ_{k,l} ≥ 0 iff D(t) ≤ G(k, l)
-- statement:
--   In the dynamic lot size model, fix periods $1 \le k < l$ and write the difference function of Lemma 2(a) as $\Delta_{k,l}(D) = A(k,l) + (c_{k,l} - c_l)\,D$. If $c_{k,l} < c_l$, then $\Delta_{k,l}$ is strictly decreasing, and for every $D \in \mathbb R$
--   $$
--   \Delta_{k,l}(D) \ge 0 \iff D \le G(k, l).
--   $$
--
--   In this case period $l$ is the better last setup period for cumulative demands below the root $G(k,l)$ and period $k$ above it (Figure 1 of the paper, right panel).
--
--   **Formalization Note.** As in Lemma 2(b), "decreasing" refers to the cumulative demand, and the comparison with $G(k,l)$ is in the extended reals.
-- source:
--   Federgruen and Tzur, A Simple Forward Algorithm to Solve General Dynamic Lot Sizing Models with n Periods in O(n log n) or O(n) Time, Management Science 37(8), 1991, p. 914, LEMMA 2(c) and Figure 1

import Mathlib
import Definitions.Def_FedergruenTzur_MinPred_Breakpoint

namespace FedergruenTzur.MinPred

open LotSizing

/-- LEMMA 2(c), p. 914: for periods `k < l`, if `c_{k,l} < c_l` then the difference function
`Δ_{k,l}`, i.e. `D ↦ A(k, l) + (c_{k,l} - c_l) D` (Lemma 2(a)), is decreasing in the cumulative demand,
and it is `≥ 0` if and only if `D ≤ G(k, l)`. -/
theorem lemma2c_decreasing (P : LotSizing) (k l : ℕ) (hk : 1 ≤ k) (hkl : k < l)
    (hc : P.cij k l < P.c l) :
    StrictAnti (fun x : ℝ => P.A k l + (P.cij k l - P.c l) * x) ∧
    ∀ x : ℝ, (0 ≤ P.A k l + (P.cij k l - P.c l) * x ↔ (x : EReal) ≤ P.G k l) := by sorry

end FedergruenTzur.MinPred
