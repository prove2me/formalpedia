-- Prove2me | Theorems.Thm_Chi2QEC_Supplement_volumeRatio_not_max_qubit
-- name    : Chi2QEC.Supplement.volumeRatio_not_max_qubit
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:09:52.168125+00:00
-- url     : https://prove2.me/theorems/da311899-120f-5916-8aba-b822483bdfe7
-- title:
--   Theorem 4 (corrected: refuted at $k=2$) — the volume ratio $b^k/q^n$ is not maximized at $b=q=2$; the bound (108) holds
-- statement:
--   For a code of $k$ logical qudits of dimension $b$ in $n$ physical qudits of dimension $q$, the volume ratio is $r=b^k/q^n$. All codes below satisfy the error-correction condition (23) for the generalized Pauli errors of weight at most $1$ and are nondegenerate for them. Then:
--
--   1. every such code with $q\ge2$ has
--   $$
--   r\le\frac1{1+n(q^2-1)}\le\frac1{1+3n},
--   $$
--   which is the bound (108) and the fact that its right-hand side is largest at $q=2$;
--   2. at $k=2$ there is such a code with $n=9$, $q=2$, $b=3$, whose volume ratio $3^2/2^9$ is strictly larger than the volume ratio $2^2/2^{n'}$ of every such code with $b=q=2$, of any length $n'$;
--   3. at $k=2$ the parameters $n=8$, $q=2$, $b=3$ satisfy $[1+n(q^2-1)]b^k\le q^n$, which is (107), and their volume ratio $3^2/2^8$ is strictly larger than $2^2/2^{n'}$ for every $n'$ at which $b=q=2$ satisfies (107).
--
--   The printed theorem says that $\max_{b,q}(r)$ is attained at $b=q=2$ for all values of $k$. Clause 2 refutes it as a statement about codes and clause 3 refutes it as a statement about the parameters permitted by the Hamming bound. Both compare with every length $n'$, the witness's own included, so both cover a fixed $n$ as well as a least $n$. Clause 1 is the part of the printed proof that is true.
--
--   **Formalization Note** The ratios are taken in $\mathbb R$. The denominators $q^n$ and $1+n(q^2-1)$ are positive for $q\ge2$.
--
--   Differences from the source:
--   - correction: "For nondegenerate [[n log2(q), k log2(b), 3]] QEC codes, max_{b,q}(r) is attained at b = q = 2 for all values of k" → the bound (108) with its maximum at q = 2, and the refutation at k = 2 both for codes and for the parameters permitted by (107); reason: false as printed: a nondegenerate ((9,9,3)) qubit code (b = 3, q = 2, k = 2) has r = 9/512, while a code with b = q = 2, k = 2 needs n ≥ 8, so r ≤ 1/64 = 8/512; for the bound alone, n = 8, b = 3, q = 2 gives 9/256 > 1/32
--   - reading: n is not quantified (qⁿ is fixed in the preceding paragraph, least in the proof), nor is it said whether r ranges over codes or over parameters permitted by (107) → clauses 2 and 3 compare with b = q = 2 at every length, the witness's own included, one clause for codes and one for (107); reason: the source is ambiguous, and this refutes every one of these readings at once
--   - reading: "[[n log2(q), k log2(b), 2t+1]] code" correcting t-qudit rotation errors (p.3) with t = 1 → finrank C = b^k, SatisfiesKL and IsNondegenerate for rotationError n q 1; reason: distance 3 = 2t + 1 with t = 1 and (23) is the paper's correctability condition
--   - encoding: qudits of dimension q; r = bᵏ/qⁿ → 2 ≤ q in clause 1; division in ℝ; reason: a qudit has q ≥ 2 states, and every denominator is then positive
-- source:
--   Niu–Chuang–Shapiro, Hardware-Efficient Bosonic QEC Codes Based on Symmetry Operators, arXiv:1709.05302v1, Theorem 4 and eqs. (107)–(108), p.16

import Mathlib
import Definitions.Def_Chi2QEC_SatisfiesKL
import Definitions.Def_Chi2QEC_IsNondegenerate
import Definitions.Def_Chi2QEC_Supplement_rotationError

namespace Chi2QEC.Supplement

/-- Niu–Chuang–Shapiro, *Hardware-Efficient Bosonic QEC Codes Based on Symmetry Operators*,
arXiv:1709.05302v1, Theorem 4 and its proof, eqs. (107)–(108), p.16, refuted. Printed: for
nondegenerate `[[n log₂ q, k log₂ b, 3]]` codes, `max_{b,q} (r)` is attained at `b = q = 2` for
all values of `k`, where `r = bᵏ/qⁿ` is the volume ratio.

Three clauses:
1. the true part of the proof, (108): every such code with `q ≥ 2` has
   `r ≤ 1/(1 + n(q² − 1)) ≤ 1/(1 + 3n)`, the right-hand side being the value at `q = 2`;
2. the refutation for codes, at `k = 2`: some such code with `n = 9`, `q = 2`, `b = 3` has volume
   ratio `3²/2⁹` strictly above that of every such code with `b = q = 2`, whatever its length;
3. the refutation for the parameters permitted by (107), at `k = 2`: `n = 8`, `q = 2`, `b = 3`
   satisfies (107) and `3²/2⁸` is strictly above `2²/2ⁿ` for every `n` at which `b = q = 2`
   satisfies (107).

**Formalization Note.** The theorem does not say whether `n` is fixed (the preceding paragraph
fixes `qⁿ`) or chosen least (as in the proof), or whether the maximum is over codes or over
parameters permitted by (107). Clauses 2–3 compare with `b = q = 2` at every length, in particular
at the witness's own, so they refute each of these readings. -/
theorem volumeRatio_not_max_qubit :
    (∀ (n q b k : ℕ) (C : Submodule ℂ (EuclideanSpace ℂ (QuditIdx n q))),
        2 ≤ q → Module.finrank ℂ C = b ^ k →
        SatisfiesKL C (rotationError n q 1) →
        IsNondegenerate C (rotationError n q 1) →
        (b : ℝ) ^ k / (q : ℝ) ^ n ≤ 1 / (1 + (n : ℝ) * ((q : ℝ) ^ 2 - 1)) ∧
          1 / (1 + (n : ℝ) * ((q : ℝ) ^ 2 - 1)) ≤ 1 / (1 + 3 * (n : ℝ))) ∧
      (∃ C : Submodule ℂ (EuclideanSpace ℂ (QuditIdx 9 2)),
        Module.finrank ℂ C = 3 ^ 2 ∧
        SatisfiesKL C (rotationError 9 2 1) ∧
        IsNondegenerate C (rotationError 9 2 1) ∧
        ∀ (n : ℕ) (C' : Submodule ℂ (EuclideanSpace ℂ (QuditIdx n 2))),
          Module.finrank ℂ C' = 2 ^ 2 →
          SatisfiesKL C' (rotationError n 2 1) →
          IsNondegenerate C' (rotationError n 2 1) →
          (2 : ℝ) ^ 2 / (2 : ℝ) ^ n < (3 : ℝ) ^ 2 / (2 : ℝ) ^ 9) ∧
      ((1 + 8 * (2 ^ 2 - 1)) * 3 ^ 2 ≤ (2 : ℕ) ^ 8 ∧
        ∀ n : ℕ, (1 + n * (2 ^ 2 - 1)) * 2 ^ 2 ≤ (2 : ℕ) ^ n →
          (2 : ℝ) ^ 2 / (2 : ℝ) ^ n < (3 : ℝ) ^ 2 / (2 : ℝ) ^ 8) := by sorry

end Chi2QEC.Supplement
