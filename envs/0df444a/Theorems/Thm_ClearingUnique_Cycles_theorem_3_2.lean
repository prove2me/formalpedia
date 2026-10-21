-- Prove2me | Theorems.Thm_ClearingUnique_Cycles_theorem_3_2
-- name    : ClearingUnique.Cycles.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:51:00.451442+00:00
-- url     : https://prove2.me/theorems/ab33a1b5-6033-45a9-931b-584d341edbdc
-- title:
--   Theorem 3.2, p. 10 — clearing matrices form a complete lattice
-- statement:
--   For a financial network $N$ satisfying the standing assumptions, let $\mathcal C$ be its set of clearing payment matrices, ordered entrywise. Every subset $S\subseteq\mathcal C$ has a least upper bound and a greatest lower bound **within $\mathcal C$**. In particular, there are a least clearing matrix $P^-$ and a greatest clearing matrix $P^+$:
--
--   $$
--   \forall P\in\mathcal C,\qquad P^-\le P\le P^+.
--   $$
--
--   The lattice result supplies the extremal matrices used throughout the paper's uniqueness argument. The empty subset is included; its bounds give the greatest and least elements.
-- source:
--   Csóka & Herings, Uniqueness of Clearing Payment Matrices in Financial Networks, GSBE Research Memorandum RM/21/014 (Maastricht University, 8 Sep 2021; doi:10.26481/umagsb.2021014), p. 10 (PDF 12), Theorem 3.2

import Mathlib
import Definitions.Def_ClearingUnique_Cycles_Model

namespace ClearingUnique.Cycles

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem theorem_3_2 (N : FinNetwork I) (hN : N.Standing) :
    (∀ S : Set (I → I → ℝ), S ⊆ {P | IsClearing N P} →
      (∃ P, IsLeast {R : I → I → ℝ | IsClearing N R ∧ ∀ Q ∈ S, Q ≤ R} P) ∧
      (∃ P, IsGreatest {R : I → I → ℝ | IsClearing N R ∧ ∀ Q ∈ S, R ≤ Q} P)) ∧
    (∃ P, IsLeast {R : I → I → ℝ | IsClearing N R} P) ∧
    (∃ P, IsGreatest {R : I → I → ℝ | IsClearing N R} P) := by sorry

end ClearingUnique.Cycles
