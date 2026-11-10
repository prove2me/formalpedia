-- Prove2me | Theorems.Thm_EvasivePatterns_equation_6_full_norm
-- name    : EvasivePatterns.equation_6_full_norm
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:28:22.446331+00:00
-- url     : https://prove2.me/theorems/618da34c-bc34-4884-8806-12882e937c55
-- title:
--   Display (6) — sign rule $q_iq_j=q_{j-i}$ and full-norm identity $\|Q_PQ_P^*\|_1=|S_P|^2$
-- statement:
--   Let $P$ be a binary word with period support $S_P$, prefix signs $q_j$ and signed period polynomial $Q_P$, and let $Q^*(z) = z^{\deg Q} Q(z^{-1})$. Then:
--
--   1. (sign rule) for $i, j \in S_P$ with $i \le j$, $q_i q_j = q_{j-i}$, where $q_{j-i}$ is the sign of the prefix of length $j - i$ (not necessarily a period);
--   2. all products contributing to a fixed coefficient of $Q_P(z) Q_P^*(z)$ have the same sign: if $i, j, i', j' \in S_P$ and $i - j = i' - j'$, then $q_i q_j = q_{i'} q_{j'}$;
--   3. (full-norm identity)
--   $$
--   \|Q_P Q_P^*\|_1 = |S_P|^2 .
--   $$
--
--   Without cancellation the norm counts the $|S_P|^2$ ordered pairs of shifts; this identity is the bridge from the distance multiset of $S_P$ to factorizations of $Q_P$.
--
--   Differences from the source:
--   - generalization: binary pattern P (the paper's patterns have a smallest period, hence are nonempty) → any P : List Bool, the empty word included; reason: the statement also holds for the empty word, so it specializes to the source's claim for every nonempty P
--   - encoding: products contributing to a fixed coefficient of Q_P(z)Q_P^*(z) → pairs (i, j), (i′, j′) in S_P with i − j = i′ − j′; reason: the product has the term q_i q_j z^{i+m−j}, so these are exactly the pairs contributing to one coefficient
--   - encoding: Q^*(z) = z^{deg Q} Q(z^{−1}) → Polynomial.reverse; reason: the same polynomial
-- source:
--   Faro, Marino, Pavone, A Complete Characterization of Eventually Evasive Binary Patterns, manuscript (Nov. 2026; sha256 e91deef3…), §2, display (6) and the two sentences before it, p.3 (PDF p.4), lines 99–102

import Mathlib
import Definitions.Def_EvasivePatterns_signedPeriodPoly
import Definitions.Def_EvasivePatterns_l1Norm

namespace EvasivePatterns

/-- **Sign rule and the full-norm identity (6).** If `i, j ∈ S_P` and `i ≤ j`, periodicity gives
`q_i q_j = q_{j−i}`, where the right-hand side refers to the sign of the length-`(j − i)` prefix (not
necessarily a period). Thus all products contributing to a fixed coefficient of `Q_P(z) Q_P^*(z)` have
the same sign. In particular `‖Q_P Q_P^*‖₁ = |S_P|²` (6), where `Q^*(z) = z^{deg Q} Q(z^{−1})`.

Source: S. Faro, F. P. Marino, A. Pavone, *A Complete Characterization of Eventually Evasive Binary
Patterns*, manuscript (Nov. 2026), §2, display (6) and the sentences before it, printed p. 3 (PDF p. 4), lines 99–102.

**Formalization Note** Binary words are `List Bool`; the statement also holds for the empty word
(`S_P = {0}`, `Q_P = 1`), which is therefore not excluded. `q_j = prefixSign P j` for every length `j`.
The product `Q_P Q_P^*` has the term `q_i q_j z^{i + m − j}` for `i, j ∈ S_P`, so two products
contribute to the same coefficient exactly when `i − j = i' − j'`; `Q_P^*` is
`Polynomial.reverse`, which is `z^m Q_P(z^{−1})` since `deg Q_P = m`; `‖·‖₁` is `l1Norm`. -/
theorem equation_6_full_norm (P : List Bool) :
    (∀ i ∈ periodSupport P, ∀ j ∈ periodSupport P, i ≤ j →
        prefixSign P i * prefixSign P j = prefixSign P (j - i)) ∧
      (∀ i ∈ periodSupport P, ∀ j ∈ periodSupport P, ∀ i' ∈ periodSupport P,
        ∀ j' ∈ periodSupport P, (i : ℤ) - j = (i' : ℤ) - j' →
          prefixSign P i * prefixSign P j = prefixSign P i' * prefixSign P j') ∧
      l1Norm (signedPeriodPoly P * (signedPeriodPoly P).reverse) =
        ((periodSupport P).card : ℤ) ^ 2 := by sorry

end EvasivePatterns
