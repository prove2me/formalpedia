-- Prove2me | Theorems.Thm_ErdosDyadic_copies_meet_C
-- name    : ErdosDyadic.copies_meet_C
-- status  : Proved
-- author  : @Jhon Lenin Acuna
-- created : 2026-11-25T04:37:23.38738+00:00
-- url     : https://prove2.me/theorems/2ba65630-4e93-45a3-90c8-c24d0d528f80
-- title:
--   Every signed affine copy of $D$ meets the dilated union $C$
-- statement:
--   Let $(H_j)_{j\ge1}$ be sets with the hitting property
--   $$\forall j\ge1\ \forall y\in\mathbb R\ \forall t\in[1,2]\ \exists n\ge1:\ y+t\,2^{-n}\in H_j,$$
--   and put
--   $$C=\bigcup_{j\ge1}\bigl(2^{-j}H_j\ \cup\ (-2^{-j}H_j)\bigr).$$
--   Then for every $x\in\mathbb R$ and every $s\ne0$ there is an integer $N\ge1$ with $x+s\,2^{-N}\in C$; that is, every nontrivial affine copy $x+sD$ meets $C$.
--
--   This is the reduction in Section 6 that converts hitting sets for scales in $[1,2]$ into a set meeting copies at every nonzero scale of either sign.
--
--   **Formalization Note** $C$ is written out inline (no separate definition). The index set $\{j\ge1\}$ is explicit; $H_0$ plays no role.
-- source:
--   OpenAI, The dyadic case of the Erdős similarity conjecture, Sept 25, 2026, https://github.com/openai/math/tree/main/preprints/The-dyadic-case-of-the-Erdos-similarity-conjecture-September-25-2026, Section 6, p. 15 (last two paragraphs of the proof of Theorem 1.1)

import Mathlib

open MeasureTheory Set

namespace ErdosDyadic

/-- Reduction step: from hitting sets H_j (j ≥ 1) every signed affine copy of D meets C. -/
theorem copies_meet_C (H : ℕ → Set ℝ)
    (hhit : ∀ j, 1 ≤ j → ∀ y : ℝ, ∀ t ∈ Icc (1 : ℝ) 2, ∃ n : ℕ, 1 ≤ n ∧
      y + t * (2 : ℝ) ^ (-(n : ℤ)) ∈ H j) :
    ∀ x s : ℝ, s ≠ 0 → ∃ N : ℕ, 1 ≤ N ∧
      x + s * (2 : ℝ) ^ (-(N : ℤ)) ∈
        ⋃ j ∈ {j : ℕ | 1 ≤ j},
          (((fun y : ℝ => (2 : ℝ) ^ (-(j : ℤ)) * y) '' H j) ∪
           ((fun y : ℝ => -((2 : ℝ) ^ (-(j : ℤ)) * y)) '' H j)) := by
  sorry

end ErdosDyadic
