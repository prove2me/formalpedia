-- Prove2me | Theorems.Thm_AlgoPFR_claim_5_4_localization
-- name    : AlgoPFR.claim_5_4_localization
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:43:00.92625+00:00
-- url     : https://prove2.me/theorems/8ec7fe14-50be-4a9d-afca-574f97f035cd
-- title:
--   Claim 5.4 — localizing a heavy coset $a+V'$ from one sample
-- statement:
--   There are a program and constants $c_0>0$, $c_1$, $c_2$, $e$ such that for every nonempty $A\subseteq\mathbb F_2^n$, every $R\ge1$ and every basis of a subspace $V$ with $d[U_A;U_V]\le R$:
--
--   1. on every run the program uses at most one sample, no membership query, and log-cost time at most $c_2(n+\log R+2)^e$;
--   2. with probability at least $c_0$ it outputs $a$, the sample it drew, and a basis of a subspace $V'\le V$ with $\dim V-\dim V'\le c_1R$, with $V'=\{0\}$ or $|V'|\le|A|/2$, and with
--   $$\frac{|A\cap(a+V')|}{|A|}\ge2^{-c_1R}.$$
--
--   This cuts a possibly too large candidate subspace down to the size required by the theorem.
--
--   Differences from the source:
--
--   - reading: poly(n) time, with R given → time polynomial in n and log R; reason: a bit-cost machine reads ⌈R⌉, which costs its bit length
--   - encoding: a basis of V, and the Ω(1), O(R) constants → a linearly independent list, with input n, ⌈R⌉, its length and the list; c₀, c₁ before n, A, R; reason: the machine's input convention and the universal constants
--   - encoding: a sampler for U_A only, and a ∼ U_A → the machine's oracles for A with the membership-query count required to be 0 on every run, and a the first element of the sample stream; reason: the machine always carries both oracles; with no query and one sample, the output point is that sample
-- source:
--   Arunachalam, Dutt, Grewal, Gupte, Marton's conjecture in polynomial time, arXiv:2609.20771 (sha256 60e45066…), Claim 5.4, p.44

import Mathlib
import Definitions.Def_AlgoPFR_Machine

set_option autoImplicit false

open scoped ENNReal Pointwise

namespace AlgoPFR

/-- **Claim 5.4.** Arunachalam, Dutt, Grewal, Gupte, *Marton's conjecture in polynomial time*, arXiv:2609.20771 (sha256 60e45066…), p.44: for nonempty `A`, `R ≥ 1` and a basis of `V` with `d[U_A;U_V] ≤ R`, an algorithm
outputs with probability `Ω(1)` an affine coset `a + V′`, with `a ∼ U_A`, `V′ ≤ V`,
`dim V′ = dim V − O(R)`, and either `V′ = {0}` or `|V′| ≤ |A|/2`, such that
`|A ∩ (a + V′)| / |A| ≥ 2^(−O(R))`. It uses `poly(n)` time and one sample from `U_A`.

**Formalization Note.** The input is `n`, `⌈R⌉`, the length of the basis, and the basis. In a bit-cost model
reading `R` costs its bit length, so "`poly(n)` time" is read as polynomial in `n` and `log R`. The output is
`a` followed by a basis of `V′`, and `a` is the first sample of the stream. The claim's algorithm is
given only a sampler for `U_A`, so the program makes no membership query on any run. -/
theorem claim_5_4_localization :
    ∃ (P : Program) (c₀ c₁ c₂ : ℝ) (e : ℕ), 0 < c₀ ∧ ∀ (n : ℕ) (A : Finset (Vec n)) (hA : A.Nonempty)
      (R : ℝ) (L : List (Vec n)), 1 ≤ R → IsBasisList L →
      rd (uniformLaw A hA) (subspaceLaw (listSpan L)) ≤ R →
      (∀ ω : Tape n, ∃ t,
        (run n P (memberRate A) (n :: ⌈R⌉₊ :: L.length :: L.map encodeVec) ω t).out.isSome ∧
        (run n P (memberRate A) (n :: ⌈R⌉₊ :: L.length :: L.map encodeVec) ω t).samples ≤ 1 ∧
        (run n P (memberRate A) (n :: ⌈R⌉₊ :: L.length :: L.map encodeVec) ω t).queries = 0 ∧
        ((run n P (memberRate A) (n :: ⌈R⌉₊ :: L.length :: L.map encodeVec) ω t).cost : ℝ) ≤
          c₂ * ((n : ℝ) + Real.logb 2 R + 2) ^ e) ∧
      ProbAtLeast (tapeMeasure (uniformLaw A hA))
        {ω | ∃ L' : List (Vec n),
          Outputs n P (memberRate A) (n :: ⌈R⌉₊ :: L.length :: L.map encodeVec) ω
            (encodeVec (ω.2.1 0) :: L'.map encodeVec) ∧
          IsBasisList L' ∧ listSpan L' ≤ listSpan L ∧
          ((Module.finrank (ZMod 2) (listSpan L) : ℝ) -
              Module.finrank (ZMod 2) (listSpan L') ≤ c₁ * R) ∧
          (listSpan L' = ⊥ ∨ 2 * subspaceCard (listSpan L') ≤ A.card) ∧
          (2 : ℝ) ^ (-(c₁ * R)) * A.card ≤ cosetCount A (ω.2.1 0) (listSpan L')} c₀ := by sorry

end AlgoPFR
