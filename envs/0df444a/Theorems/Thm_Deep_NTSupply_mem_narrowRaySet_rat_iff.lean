-- Prove2me | Theorems.Thm_Deep_NTSupply_mem_narrowRaySet_rat_iff
-- name    : Deep.NTSupply.mem_narrowRaySet_rat_iff
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T23:04:52.969711+00:00
-- url     : https://prove2.me/theorems/d036645e-333f-4d71-bd3d-dc2ab4fdd1bc
-- title:
--   Narrow ray principal generators over Q are positive and congruent to 1
-- statement:
--   Let $n$ be a nonnegative integer and let $I$ be a nonzero fractional ideal of $\mathbb Q$. It belongs to the generating set of the narrow ray subgroup at modulus $(n)$ precisely when it is a principal ideal $(a)$ for an integer $a>0$ satisfying $a\equiv1\pmod n$. The existential witness is kept in $\mathcal O_{\mathbb Q}$, with its image in $\mathbb Z$ used for positivity and congruence. The result is the concrete form of the defining relation needed to compare the narrow ray group of $\mathbb Q$ with $(\mathbb Z/n\mathbb Z)^\times$.
-- source:
--   Definitions.Def_NarrowRayClassGroup, definition Deep.NTSupply.narrowRaySet and lemma mem_narrowRaySet_iff (the defining positivity and modulus clauses); Mathlib NumberTheory/NumberField/Basic, Rat.ringOfIntegersEquiv, https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/NumberField/Basic.html .

import Definitions.Def_NarrowRayClassGroup
import Theorems.Thm_Rat_ringOfIntegers_pos_iff_all_real_embeddings
import Theorems.Thm_Rat_mem_span_nat_iff_congruence

open NumberField nonZeroDivisors

namespace Deep.NTSupply
theorem mem_narrowRaySet_rat_iff (n : ℕ)
    (I : (FractionalIdeal ((NumberField.RingOfIntegers ℚ)⁰) ℚ)ˣ) :
    I ∈ narrowRaySet ℚ (Ideal.span {(n : NumberField.RingOfIntegers ℚ)}) ↔
      ∃ a : NumberField.RingOfIntegers ℚ, a ≠ 0 ∧
        0 < Rat.ringOfIntegersEquiv a ∧
        (∃ k : ℤ, Rat.ringOfIntegersEquiv a = 1 + (n : ℤ) * k) ∧
        (I : FractionalIdeal ((NumberField.RingOfIntegers ℚ)⁰) ℚ) =
          ((Ideal.span {a} : Ideal (NumberField.RingOfIntegers ℚ)) :
            FractionalIdeal ((NumberField.RingOfIntegers ℚ)⁰) ℚ) := by sorry
end Deep.NTSupply
