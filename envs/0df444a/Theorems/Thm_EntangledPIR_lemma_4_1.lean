-- Prove2me | Theorems.Thm_EntangledPIR_lemma_4_1
-- name    : EntangledPIR.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:09:40.300319+00:00
-- url     : https://prove2.me/theorems/3dc41fa8-a77f-4b33-927f-5fc4732232d9
-- title:
--   Lemma 4.1 — correctness of one copy
-- statement:
--   Let $g:\{0,1\}^d\to\{0,1\}^m$ and $a,b\in\{0,1\}^d$, and let the servers share the Bell pairs of one copy. Suppose that A performs its operation with mask $a$, that B performs the computation with mask $b$ and sends $K$ and $v$, and that A then measures $\mathsf Y_K$ and obtains $u$. Then, with probability one,
--
--   $$u\oplus v=g(a\oplus b).$$
--
--   This holds in either order of the operation of A and the computation of B, and whether or not A measures $\mathsf P$. It is the correctness of the basic lookup, on which Protocol 1 runs each query.
--
--   Differences from the source:
--   - encoding: finite-dimensional registers and tensor products → finite basis types, `Matrix` on them and `⊗ₖ`; reason: Lean convention; a register is its computational basis, same operators
--   - encoding: $\{0,1\}^d$ and $\oplus$ → `Fin d → Bool` and coordinatewise `xor`; reason: Lean convention; same strings
--   - encoding: "with probability one", "in either order", "whether or not" → every branch with $u\oplus v\ne g(a\oplus b)$ has amplitude zero, in both orders of the products and for both Kraus forms, and the probabilities of all branches sum to one; reason: the amplitude of a branch determines its probability; the total makes the first claim non-vacuous
-- source:
--   Mantri, Private Information Retrieval from Two Entangled Servers, manuscript (Nov. 2026; sha256 5cfce27c…51384), Lemma 4.1, p.20

import Definitions.Def_EntangledPIR_testProj

open Matrix

namespace EntangledPIR

/-- **Lemma 4.1 (Correctness of One Copy)**, Mantri, manuscript (Nov. 2026), p.20. For
`g : {0,1}^d → {0,1}^m` and masks `a, b`, in the state of the Bell pairs of one copy: A performs its
operation with mask `a` (the Kraus operator `A₁`, either `opKraus g a e`, with `P` measured, or `U_g X^a_P`,
without), B performs the computation with mask `b`, with outcomes `J`, `v`, and A then measures `Y_K` for
`K = J ⊕ b`, obtaining `u`. Every branch with `u ⊕ v ≠ g(a ⊕ b)` has amplitude zero, in either order of the
operation of A and the computation of B, and the probabilities of all branches sum to one.

**Formalization Note.** Each claim is stated for both orders, `·AB` and `·BA`, and for both forms of `A₁`.
The total probability makes the first claim non-vacuous. -/
theorem lemma_4_1 {d m : ℕ} (g : Bits d → Bits m) (a b : Bits d) :
    (∀ e J (u v : Bits m), bxor u v ≠ g (bxor a b) →
      (leftOp (outProj (bxor J b) u) * leftOp (opKraus g a e) * rightOp (computeKraus b J v)) *ᵥ
          bellCopy d m = 0 ∧
      (leftOp (outProj (bxor J b) u) * rightOp (computeKraus b J v) * leftOp (opKraus g a e)) *ᵥ
          bellCopy d m = 0) ∧
    (∀ J (u v : Bits m), bxor u v ≠ g (bxor a b) →
      (leftOp (outProj (bxor J b) u) * leftOp (Ug g * onAddr (pauliXs a)) *
          rightOp (computeKraus b J v)) *ᵥ bellCopy d m = 0 ∧
      (leftOp (outProj (bxor J b) u) * rightOp (computeKraus b J v) *
          leftOp (Ug g * onAddr (pauliXs a))) *ᵥ bellCopy d m = 0) ∧
    (∑ e, ∑ J, ∑ u : Bits m, ∑ v : Bits m,
      normSq ((leftOp (outProj (bxor J b) u) * leftOp (opKraus g a e) *
        rightOp (computeKraus b J v)) *ᵥ bellCopy d m) = 1) ∧
    (∑ e, ∑ J, ∑ u : Bits m, ∑ v : Bits m,
      normSq ((leftOp (outProj (bxor J b) u) * rightOp (computeKraus b J v) *
        leftOp (opKraus g a e)) *ᵥ bellCopy d m) = 1) ∧
    (∑ J, ∑ u : Bits m, ∑ v : Bits m,
      normSq ((leftOp (outProj (bxor J b) u) * leftOp (Ug g * onAddr (pauliXs a)) *
        rightOp (computeKraus b J v)) *ᵥ bellCopy d m) = 1) ∧
    (∑ J, ∑ u : Bits m, ∑ v : Bits m,
      normSq ((leftOp (outProj (bxor J b) u) * rightOp (computeKraus b J v) *
        leftOp (Ug g * onAddr (pauliXs a))) *ᵥ bellCopy d m) = 1) := by sorry

end EntangledPIR
