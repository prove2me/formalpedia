-- Prove2me | Theorems.Thm_DiazModulus_log_ratio_multipliers
-- name    : DiazModulus.log_ratio_multipliers
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T18:24:04.084037+00:00
-- url     : https://prove2.me/theorems/b8695f38-8a74-4b70-a4d5-f2e3888fd4b9
-- title:
--   What the ratio of two commensurable logarithms multiplies into ℒ
-- statement:
--   **Multipliers of a commensurable ratio of logarithms.**
--
--   Let $u, v$ be non-zero logarithms of algebraic numbers with $|u|^{2} = c\,|v|^{2}$ for a rational $c$. Suppose $v$ is neither a rational multiple of $u$ nor of $\bar u$. If $w$ and $uw/v$ are also logarithms of algebraic numbers, then
--
--   $$w \in \mathbb{Q}\,v + \mathbb{Q}\,\bar u .$$
--
--   The reverse inclusion is immediate, since $(u/v)\,\bar u = c\,\bar v$. For a single candidate of Diaz's conjecture, the six exponentials theorem is powerless: `DiazModulus.sixExponentials_cannot_refute_candidate` records that a candidate certifies only a three-dimensional space. With two candidates of commensurable moduli it starts to work. The ratio $u/v$ carries both $v$ and $\bar u$ back into the logarithms, which supplies two columns of a rank-one $2\times3$ array. The main consequence is `DiazModulus.candidate_quotient_rigid`.
--
--   **Novelty.** The statement is a short consequence of the six exponentials theorem. Novelty is not asserted.
-- source:
--   Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.9, 25 September 2026 (GitHub release note-v1.9), Theorem 6.9. Novelty is not asserted. Formal proof: Diaz modulus mission, 23 September 2026 (C. Perassi). Background: the six exponentials theorem (S. Lang, 1966; K. Ramachandra, 1968).

import Mathlib

open ComplexConjugate

namespace DiazModulus

theorem log_ratio_multipliers (u v w : ℂ) (hu : u ≠ 0) (hv : v ≠ 0)
    (heu : IsAlgebraic ℚ (Complex.exp u)) (hev : IsAlgebraic ℚ (Complex.exp v))
    (hew : IsAlgebraic ℚ (Complex.exp w))
    (c : ℚ) (hc : u * conj u = (c : ℂ) * (v * conj v))
    (hvu : ∀ q : ℚ, v ≠ (q : ℂ) * u) (hvu' : ∀ q : ℚ, v ≠ (q : ℂ) * conj u)
    (hm : IsAlgebraic ℚ (Complex.exp (u * w / v))) :
    ∃ a b : ℚ, w = (a : ℂ) * v + (b : ℂ) * conj u := by sorry

end DiazModulus
