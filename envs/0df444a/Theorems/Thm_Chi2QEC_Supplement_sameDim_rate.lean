-- Prove2me | Theorems.Thm_Chi2QEC_Supplement_sameDim_rate
-- name    : Chi2QEC.Supplement.sameDim_rate
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:08:53.191965+00:00
-- url     : https://prove2.me/theorems/a83c7219-22d1-49d6-95a9-a2430d3a8a81
-- title:
--   Theorem 2 (corrected: the maximum rate is $1/5$, not $1/4$) — same-dimension codes with $k=t=1$, and the $n=4$, $q\ge4$ threshold of the Hamming bound
-- statement:
--   Let $q\ge2$. Consider nondegenerate $[[n\log_2 q,\log_2 q,3]]$ codes: codes $C\subseteq(\mathbb C^q)^{\otimes n}$ of dimension $q$ (one logical qudit of the same dimension as the physical ones) that satisfy the error-correction condition (23) for all generalized Pauli errors of weight at most $1$ and are nondegenerate for them. Then:
--
--   1. every such code has $n\ge5$;
--   2. such a code with $n=5$ exists, so the maximum of $1/n$ over these codes is $1/5$;
--   3. the qudit-rotation Hamming bound (102) at $b=q$, $k=t=1$, namely $(1+n(q^2-1))\,q\le q^n$, forces $n\ge4$;
--   4. at $n=4$ that bound, $\big(1+4(q^2-1)\big)q\le q^4$, holds if and only if $q\ge4$.
--
--   The printed theorem says that for nondegenerate codes of this kind $\max_q(1/n)=1/4$ is achieved for $q\ge4$. It is false: by clause 1 no such code has $n=4$, for any $q$. Clauses 1–2 are the corrected theorem about codes. Clauses 3–4 are what the printed proof establishes: $1/4$ is the largest value of $1/n$ that the bound (102) permits, and it permits it exactly for $q\ge4$.
--
--   **Formalization Note** Clauses 3 and 4 are written as instances of the sum $\sum_{j=0}^{1}\binom nj(q^2-1)^j$ in (102), not in closed form.
--
--   Differences from the source:
--   - correction: "For nondegenerate [[n log2(q), log2(q), 3]] QEC codes, max_q(1/n) = 1/4 is achieved for q ≥ 4" → every such code has 5 ≤ n and, for every q ≥ 2, one has n = 5 (maximum 1/5); separately, the bound (102) forces 4 ≤ n and holds at n = 4 iff 4 ≤ q; reason: false as printed: for q = 4 (indeed every q ≥ 2) no code of dimension q on n = 4 qudits corrects one error, since the quantum Singleton bound q^(n−4) ≥ q fails; the five-qudit code attains n = 5; the printed proof only evaluates (105), which the last two clauses keep
--   - reading: "[[n log2(q), k log2(b), 2t+1]] code" correcting t-qudit rotation errors (p.3) with k = t = 1, b = q → finrank C = q, SatisfiesKL and IsNondegenerate for rotationError n q 1; reason: distance 3 = 2t + 1 with t = 1, (23) is the paper's correctability condition, and rotation errors are spanned by the generalized Paulis
--   - reading: qudits of dimension q, the proof's "all q ≥ 2" → hypothesis 2 ≤ q; reason: the proof's range; at q = 1 a qudit has one state and the one-dimensional code with n = 0 satisfies every hypothesis
--   - encoding: the maximum of 1/n → a lower bound on n in ℕ, with a code attaining it; reason: 1/n is largest where n is least; the clauses exclude n = 0
-- source:
--   Niu–Chuang–Shapiro, Hardware-Efficient Bosonic QEC Codes Based on Symmetry Operators, arXiv:1709.05302v1, Theorem 2 and eq. (105), p.16

import Mathlib
import Definitions.Def_Chi2QEC_SatisfiesKL
import Definitions.Def_Chi2QEC_IsNondegenerate
import Definitions.Def_Chi2QEC_Supplement_rotationError

namespace Chi2QEC.Supplement

/-- Niu–Chuang–Shapiro, *Hardware-Efficient Bosonic QEC Codes Based on Symmetry Operators*,
arXiv:1709.05302v1, Theorem 2 and its proof, eq. (105), p.16, corrected. Printed: for
nondegenerate `[[n log₂ q, log₂ q, 3]]` codes, `max_q (1/n) = 1/4` is achieved for `q ≥ 4`.

Four clauses, for every `q ≥ 2`:
1. every code `C ≤ (ℂ^q)^{⊗n}` of dimension `q` (one logical qudit, `b = q`, `k = 1`) satisfying
   (23) and nondegenerate for the single-qudit rotation errors (`t = 1`) has `n ≥ 5`;
2. such a code exists with `n = 5`, so the maximum of `1/n` over these codes is `1/5`;
3. the bound (102) at `b = q`, `k = t = 1` forces `n ≥ 4`;
4. at `n = 4` that bound holds if and only if `q ≥ 4`.

**Formalization Note.** The printed theorem is false: by clause 1 no such code has `n = 4`
(quantum Singleton bound), so `1/4` is achieved for no `q`. Clauses 1–2 are the corrected theorem
about codes. Clauses 3–4 are what the printed proof shows about the parameters permitted by
(102), each written as an instance of the sum in (102). -/
theorem sameDim_rate (q : ℕ) (hq : 2 ≤ q) :
    (∀ (n : ℕ) (C : Submodule ℂ (EuclideanSpace ℂ (QuditIdx n q))),
        Module.finrank ℂ C = q →
        SatisfiesKL C (rotationError n q 1) →
        IsNondegenerate C (rotationError n q 1) → 5 ≤ n) ∧
      (∃ C : Submodule ℂ (EuclideanSpace ℂ (QuditIdx 5 q)),
        Module.finrank ℂ C = q ∧
        SatisfiesKL C (rotationError 5 q 1) ∧
        IsNondegenerate C (rotationError 5 q 1)) ∧
      (∀ n : ℕ,
        (∑ j ∈ Finset.range (1 + 1), n.choose j * (q ^ 2 - 1) ^ j) * q ^ 1 ≤ q ^ n → 4 ≤ n) ∧
      ((∑ j ∈ Finset.range (1 + 1), Nat.choose 4 j * (q ^ 2 - 1) ^ j) * q ^ 1 ≤ q ^ 4 ↔
        4 ≤ q) := by sorry

end Chi2QEC.Supplement
