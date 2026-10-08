-- Prove2me | Theorems.Thm_FedergruenTzur_MinPred_lemma2b_increasing
-- name    : FedergruenTzur.MinPred.lemma2b_increasing
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:53:09.021617+00:00
-- url     : https://prove2.me/theorems/0a452ce1-be18-4d38-b03e-82d638210789
-- title:
--   LEMMA 2(b): if c_{k,l} > c_l then Δ_{k,l} is increasing and Δ_{k,l} ≥ 0 iff D(t) ≥ G(k, l)
-- statement:
--   In the dynamic lot size model, fix periods $1 \le k < l$ and write the difference function of Lemma 2(a) as $\Delta_{k,l}(D) = A(k,l) + (c_{k,l} - c_l)\,D$, a function of the cumulative demand $D$. If $c_{k,l} > c_l$, then $\Delta_{k,l}$ is strictly increasing, and for every $D \in \mathbb R$
--   $$
--   \Delta_{k,l}(D) \ge 0 \iff D \ge G(k, l).
--   $$
--
--   In this case period $l$ is the better last setup period for cumulative demands above the root $G(k,l)$ and period $k$ below it (Figure 1 of the paper, left panel).
--
--   **Formalization Note.** "Increasing" is read as increasing in the cumulative demand, as plotted in the paper's Figure 1; by Lemma 2(a), $\Delta_{k,l}(t)$ is this function evaluated at $D = D(t)$, and the statement holds at every real $D$. The comparison $D \ge G(k,l)$ is in the extended reals.
-- source:
--   Federgruen and Tzur, A Simple Forward Algorithm to Solve General Dynamic Lot Sizing Models with n Periods in O(n log n) or O(n) Time, Management Science 37(8), 1991, p. 914, LEMMA 2(b) and Figure 1

import Mathlib
import Definitions.Def_FedergruenTzur_MinPred_Breakpoint

namespace FedergruenTzur.MinPred

open LotSizing

/-- LEMMA 2(b), p. 914: for periods `k < l`, if `c_{k,l} > c_l` then the difference function
`Δ_{k,l}`, i.e. `D ↦ A(k, l) + (c_{k,l} - c_l) D` (Lemma 2(a)), is increasing in the cumulative demand,
and it is `≥ 0` if and only if `D ≥ G(k, l)`. -/
theorem lemma2b_increasing (P : LotSizing) (k l : ℕ) (hk : 1 ≤ k) (hkl : k < l)
    (hc : P.c l < P.cij k l) :
    StrictMono (fun x : ℝ => P.A k l + (P.cij k l - P.c l) * x) ∧
    ∀ x : ℝ, (0 ≤ P.A k l + (P.cij k l - P.c l) * x ↔ P.G k l ≤ (x : EReal)) := by sorry

end FedergruenTzur.MinPred
