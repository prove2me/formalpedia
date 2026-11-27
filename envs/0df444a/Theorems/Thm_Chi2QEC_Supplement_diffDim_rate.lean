-- Prove2me | Theorems.Thm_Chi2QEC_Supplement_diffDim_rate
-- name    : Chi2QEC.Supplement.diffDim_rate
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:09:28.763601+00:00
-- url     : https://prove2.me/theorems/2b64efa5-9fa3-5131-a2fb-692fb18eb4b0
-- title:
--   Theorem 3 (corrected: the maximum rate is $1/5$, not $1/3$) — codes with $b\ge2$, $k=t=1$, and the $n=3$, $b=2$, $q\ge6$ threshold of the Hamming bound
-- statement:
--   Let $q\ge2$. Consider nondegenerate $[[n\log_2 q,\log_2 b,3]]$ codes: codes $C\subseteq(\mathbb C^q)^{\otimes n}$ of dimension $b\ge2$ (one logical qudit of dimension $b$, possibly different from $q$) that satisfy the error-correction condition (23) for all generalized Pauli errors of weight at most $1$ and are nondegenerate for them. Then:
--
--   1. every such code has $n\ge5$;
--   2. such a code with $n=5$ and $b=2$ exists, so the maximum of $1/n$ over these codes is $1/5$ and it is achieved with $b=2$;
--   3. for every $b\ge2$ the qudit-rotation Hamming bound (102) at $k=t=1$, namely $(1+n(q^2-1))\,b\le q^n$, forces $n\ge3$;
--   4. at $n=3$, $b=2$ that bound, $2\big(1+3(q^2-1)\big)\le q^3$, holds if and only if $q\ge6$.
--
--   The printed theorem says that for nondegenerate codes of this kind $\max_b(1/n)=1/3$ is achieved with $b=2$ for all $q\ge6$. It is false: by clause 1 no such code has $n=3$, for any $q$. Clauses 1–2 are the corrected theorem about codes. Clauses 3–4 are what the printed proof establishes: $1/3$ is the largest value of $1/n$ that the bound (102) permits, and with $b=2$ it permits it exactly for $q\ge6$.
--
--   **Formalization Note** Clauses 3 and 4 are written as instances of the sum $\sum_{j=0}^{1}\binom nj(q^2-1)^j$ in (102), not in closed form. The proof's intermediate claim that for $n=2$ (106) is equivalent to $(2b-1)q^2-1\le0$ has a slip (it is $(2b-1)q^2-b\le0$); clause 3 is unaffected.
--
--   Differences from the source:
--   - correction: "For nondegenerate [[n log2(q), log2(b), 3]] QEC codes, max_b(1/n) = 1/3 is achieved with b = 2 for all q ≥ 6" → every such code has 5 ≤ n and, for every q ≥ 2, one with b = 2 has n = 5 (maximum 1/5); separately, the bound (102) forces 3 ≤ n and holds at n = 3, b = 2 iff 6 ≤ q; reason: false as printed: for q = 6 (indeed every q ≥ 2) and b ≥ 2 no code on n = 3 qudits corrects one error, since two qudits and their one-qudit complement would both recover the logical state (quantum Singleton bound); a two-dimensional subcode of the five-qudit code attains n = 5; the printed proof only evaluates (106), which the last two clauses keep
--   - reading: "[[n log2(q), k log2(b), 2t+1]] code" correcting t-qudit rotation errors (p.3) with k = t = 1 and the maximum over b → 2 ≤ b, finrank C = b, SatisfiesKL and IsNondegenerate for rotationError n q 1; reason: distance 3 = 2t + 1 with t = 1, and the proof takes b ≥ 2 (a one-dimensional logical space encodes nothing)
--   - reading: qudits of dimension q, the proof's "q ≥ 2" → hypothesis 2 ≤ q; reason: the proof's range; a qudit of dimension 1 carries no information
--   - encoding: the maximum of 1/n → a lower bound on n in ℕ, with a code attaining it; reason: 1/n is largest where n is least; the clauses exclude n = 0
-- source:
--   Niu–Chuang–Shapiro, Hardware-Efficient Bosonic QEC Codes Based on Symmetry Operators, arXiv:1709.05302v1, Theorem 3 and eq. (106), p.16

import Mathlib
import Definitions.Def_Chi2QEC_SatisfiesKL
import Definitions.Def_Chi2QEC_IsNondegenerate
import Definitions.Def_Chi2QEC_Supplement_rotationError

namespace Chi2QEC.Supplement

/-- Niu–Chuang–Shapiro, *Hardware-Efficient Bosonic QEC Codes Based on Symmetry Operators*,
arXiv:1709.05302v1, Theorem 3 and its proof, eq. (106), p.16, corrected. Printed: for
nondegenerate `[[n log₂ q, log₂ b, 3]]` codes, `max_b (1/n) = 1/3` is achieved with `b = 2` for
all `q ≥ 6`.

Four clauses, for every `q ≥ 2`:
1. every code `C ≤ (ℂ^q)^{⊗n}` of dimension `b ≥ 2` (one logical qudit of dimension `b`, `k = 1`)
   satisfying (23) and nondegenerate for the single-qudit rotation errors (`t = 1`) has `n ≥ 5`;
2. such a code exists with `n = 5` and `b = 2`, so the maximum of `1/n` over these codes is `1/5`
   and it is achieved with `b = 2`;
3. the bound (102) at `k = t = 1` and `b ≥ 2` forces `n ≥ 3`;
4. at `n = 3`, `b = 2` that bound holds if and only if `q ≥ 6`.

**Formalization Note.** The printed theorem is false: by clause 1 no such code has `n = 3`
(quantum Singleton bound), so `1/3` is achieved for no `q`. Clauses 1–2 are the corrected theorem
about codes. Clauses 3–4 are what the printed proof shows about the parameters permitted by
(102), each written as an instance of the sum in (102). The restriction `b ≥ 2` is the proof's
("cannot be satisfied for b ≥ 2 and q ≥ 2"). -/
theorem diffDim_rate (q : ℕ) (hq : 2 ≤ q) :
    (∀ (n b : ℕ) (C : Submodule ℂ (EuclideanSpace ℂ (QuditIdx n q))),
        2 ≤ b → Module.finrank ℂ C = b →
        SatisfiesKL C (rotationError n q 1) →
        IsNondegenerate C (rotationError n q 1) → 5 ≤ n) ∧
      (∃ C : Submodule ℂ (EuclideanSpace ℂ (QuditIdx 5 q)),
        Module.finrank ℂ C = 2 ∧
        SatisfiesKL C (rotationError 5 q 1) ∧
        IsNondegenerate C (rotationError 5 q 1)) ∧
      (∀ n b : ℕ, 2 ≤ b →
        (∑ j ∈ Finset.range (1 + 1), n.choose j * (q ^ 2 - 1) ^ j) * b ^ 1 ≤ q ^ n → 3 ≤ n) ∧
      ((∑ j ∈ Finset.range (1 + 1), Nat.choose 3 j * (q ^ 2 - 1) ^ j) * 2 ^ 1 ≤ q ^ 3 ↔
        6 ≤ q) := by sorry

end Chi2QEC.Supplement
