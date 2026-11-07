-- Prove2me | Theorems.Thm_CallCountPOPBR_claim_1
-- name    : CallCountPOPBR.claim_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:05:12.024415+00:00
-- url     : https://prove2.me/theorems/719b3454-6f42-4efc-b996-da8a5608e6b8
-- title:
--   Claim 1 — free nodes are light: $\mathrm{wt}(F_k)\le 2k(k+1)\le 2n^2$
-- statement:
--   Let $F_1,\dots,F_K$ be natural numbers such that each $F_k$ is a sum $x+y$ of two numbers, each of which is a power of two or an earlier $F_i$ ($1\le i<k$). Then for $1\le k\le K$,
--   $$
--   \mathrm{wt}(F_k)\le 2k(k+1),
--   $$
--   and $2k(k+1)\le 2n^2$ for every $n\ge K+1$.
--
--   Here $\mathrm{wt}$ is the number of ones in the binary expansion. In the reduction, the $E$-values of the free nodes satisfy the hypothesis, so they have weight at most $2n^2=R/2$.
--
--   Differences from the source:
--   - generalization: operands from the pool P = {2⁰, …, 2^{a_z}} ∪ {F_1, …, F_{k−1}} → operands any power of two or an earlier F_i; reason: the proof never uses the upper limit a_z; the paper's free nodes satisfy the hypothesis
--   - reading: F_1, …, F_K are the free nodes of a completion; k ≤ K ≤ n − 1 gives the second inequality → an abstract sequence F with the operand hypothesis; the second inequality 2k(k + 1) ≤ 2n² for every n ≥ K + 1; reason: the claim's content as a lemma about sequences, so that it can be applied to any completion
-- source:
--   Swain, Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and Partial-Observation Reconstruction, STOC 2027 submission (manuscript sha256 79135884dd262e4297079b8d2f7adb5deec1b329582779ed16decf34adae2411), proof of Theorem 2.8, Claim 1, p.6

import Definitions.Def_CallCountPOPBR_wt

set_option autoImplicit false

namespace CallCountPOPBR

/-- **Claim 1 (free nodes are light).** Swain, *Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and
Partial-Observation Reconstruction*, STOC 2027 submission (manuscript sha256 79135884…), proof of Theorem 2.8, Claim 1, p.6:
"wt(F_k) ≤ 2k(k + 1) ≤ 2n². Indeed, let Λ_k be the set of exponents of the powers used directly
as operands by F_1, …, F_k; |Λ_k| ≤ 2k. By induction F_k = ∑_{e ∈ Λ_k} c_e 2^e with integers
0 ≤ c_e ≤ 2^k … and k ≤ K ≤ n − 1 gives the second inequality."

Let `F_1, …, F_K` be natural numbers such that each `F_k` is a sum `x + y` of two numbers, each a
power of two or an earlier `F_i` (`1 ≤ i < k`). Then `wt(F_k) ≤ 2k(k + 1)` for `1 ≤ k ≤ K`, and
`2k(k + 1) ≤ 2n²` whenever `K ≤ n − 1`.

**Formalization Note.** The paper's operands are powers from the pool `P = {2^0, …, 2^{a_z}}`;
here any power of two is allowed, which contains the paper's case. -/
theorem claim_1 (F : ℕ → ℕ) (K : ℕ)
    (hF : ∀ k, 1 ≤ k → k ≤ K → ∃ x y, F k = x + y ∧
      ((∃ e, x = 2 ^ e) ∨ ∃ i, 1 ≤ i ∧ i < k ∧ x = F i) ∧
      ((∃ e, y = 2 ^ e) ∨ ∃ i, 1 ≤ i ∧ i < k ∧ y = F i)) :
    ∀ k, 1 ≤ k → k ≤ K →
      wt (F k) ≤ 2 * k * (k + 1) ∧ ∀ n, K + 1 ≤ n → 2 * k * (k + 1) ≤ 2 * n ^ 2 := by sorry

end CallCountPOPBR
