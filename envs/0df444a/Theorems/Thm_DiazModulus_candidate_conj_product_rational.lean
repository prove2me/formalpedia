-- Prove2me | Theorems.Thm_DiazModulus_candidate_conj_product_rational
-- name    : DiazModulus.candidate_conj_product_rational
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T18:33:55.936711+00:00
-- url     : https://prove2.me/theorems/43395911-07c3-4558-9c7d-bf1a490ade25
-- title:
--   Two candidates whose product has algebraic real part are conjugate up to a rational factor
-- statement:
--   **Candidates at algebraic distance through conjugation.**
--
--   Let $p$ and $q$ be candidates for Diaz's conjecture: non-zero, with algebraic modulus and algebraic exponential. If $\operatorname{Re}(pq)$ is algebraic, then
--
--   $$q \in \mathbb{Q}\,\bar p .$$
--
--   Equivalently, since $|p + \bar q|^{2} = |p|^{2} + |q|^{2} + 2\operatorname{Re}(pq)$, a candidate $p$ lies at algebraic distance from $-\bar q$ only when $q$ is a rational multiple of $\bar p$. It extends `DiazModulus.candidate_distance_transcendental` from algebraic points to pairs of candidates. Like every exclusion in this mission it concerns hypothetical counterexamples, and it is vacuous if Diaz's conjecture holds.
--
--   **Novelty.** The statement is a short consequence of the Gelfond–Schneider theorem. Novelty is not asserted.
-- source:
--   Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.9, 25 September 2026 (GitHub release note-v1.9), Section 6, the first of the two lemmas stated after Theorem 6.9. Novelty is not asserted. Formal proof: Diaz modulus mission, 23 September 2026 (C. Perassi). Background: the Gelfond-Schneider theorem (1934); formal proof by M. Karatarakis and F. Wiedijk, arXiv:2603.24823.

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem candidate_conj_product_rational (p q : ℂ) (hp : IsCandidate p) (hq : IsCandidate q)
    (hre : IsAlgebraic ℚ (((p * q).re : ℝ) : ℂ)) :
    ∃ r : ℚ, q = (r : ℂ) * conj p := by sorry

end DiazModulus
