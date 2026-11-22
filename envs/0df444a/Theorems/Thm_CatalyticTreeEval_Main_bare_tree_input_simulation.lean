-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_bare_tree_input_simulation
-- name    : CatalyticTreeEval.Main.bare_tree_input_simulation
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T23:22:51.816793+00:00
-- url     : https://prove2.me/theorems/883d2582-aee6-4c95-9806-07e450b1925e
-- title:
--   Corollary 4.7 — bare-input simulation with a printed parameter header
-- statement:
--   Let $M_0$ compute a tree's root label when its input is the concatenation of a frame parameter header and the bare self-delimiting tree encoding. Assume a fixed charged printer can produce precisely that parameter header from the bare tree encoding, using $O(s)$ work and $2^{O(s)}$ time. Then one fixed finite machine $M$ supplies the same interface on the bare tree encoding alone.
--
--   For every valid frame parameter and every height-$h$ instance, if $M_0$ has simultaneous free-space, catalytic and time bounds $S,C,T$, then $M$ preserves the catalytic bound and root output, restores every arbitrary initial catalyst, and has bounds
--   $$
--   O(S+s+1),\qquad C,\qquad (T+1)\,2^{O(s)}.
--   $$
--   The same `ComputesPrefix` contract applies to all longer catalytic tapes, and every accessed catalyst cell remains in the same bounded prefix. The construction composes the parameter printer with an actual finite-state simulation of $M_0$ in which virtual input positions before the header are served from the printed header and later positions are sought on the real input. Thus no equality between the plain and header-prefixed input strings is assumed.
-- source:
--   Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533, proof of Corollary 4.7, printed pp. 26–27 (PDF pp. 28–29), in particular the one-time uniform parameter setup and Remark 3.8's time-from-space convention; finite catalytic machine model, Definitions 3.1–3.2, printed p. 14 (PDF p. 16); Section 4 input access, printed p. 25 (PDF p. 27).

import Definitions.Def_CatalyticTreeEval_Main_Framework

set_option autoImplicit false

/-- Simulate a machine expecting a uniform parameter header on the bare tree input. -/
theorem CatalyticTreeEval.Main.bare_tree_input_simulation
    (F : List Bool → Frame) (domain : Set (List Bool)) (M0 MP : Machine)
    (Ch Cht : ℝ) (r : ℕ) (hCh : 0 < Ch) (hCht : 0 < Cht) (hr : 0 < r)
    (hparam : ∀ a ∈ domain, ∀ h : ℕ, 0 < h → ∀ I : Tree (F a).l h,
      PrintsIn MP I.encode (listCode ((F a).params a))
        (Ch * (F a).s) (Cht * ((2 : ℝ) ^ (F a).s + 1) ^ r)) :
    ∃ (M : Machine) (Cs Ct : ℝ) (q : ℕ),
      0 < Cs ∧ 0 < Ct ∧ 0 < q ∧
      ∀ a ∈ domain, ∀ h : ℕ, 0 < h → ∀ I : Tree (F a).l h,
      ∀ S C T : ℝ, 0 ≤ S → 0 ≤ C → 0 ≤ T →
      ComputesPrefix M0 (listCode ((F a).params a) ++ I.encode)
        (bits (F a).l I.value.val) S C T →
      ComputesPrefix M I.encode (bits (F a).l I.value.val)
        (Cs * (S + (F a).s + 1)) C
        (Ct * (T + 1) * ((2 : ℝ) ^ (F a).s + 1) ^ q) := by sorry
