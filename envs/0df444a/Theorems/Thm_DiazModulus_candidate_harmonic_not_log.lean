-- Prove2me | Theorems.Thm_DiazModulus_candidate_harmonic_not_log
-- name    : DiazModulus.candidate_harmonic_not_log
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T18:24:26.603296+00:00
-- url     : https://prove2.me/theorems/1f90b07d-278d-4769-8ecb-7df6c8df5ab2
-- title:
--   For a candidate u, |u|²/(pu + qū) is not a logarithm of an algebraic number
-- statement:
--   **Harmonic means of a candidate and its conjugate.**
--
--   Let $u$ be a candidate for Diaz's conjecture and let $p, q$ be non-zero rationals. Then
--
--   $$e^{|u|^{2}/(pu + q\bar u)} \ \text{is transcendental.}$$
--
--   For $p = q = \tfrac12$ this says that the harmonic mean $2u\bar u/(u + \bar u) = |u|^{2}/\operatorname{Re}u$ of $u$ and $\bar u$ is not a logarithm of an algebraic number. It is an unconditional exclusion outside the candidate's hull, from the matrix $\begin{pmatrix} u & m\\ pu + q\bar u & \bar u\end{pmatrix}$ with $m = |u|^{2}/(pu + q\bar u)$. The exclusions `DiazModulus.candidate_multiplier_module` rest on Roy's strong six exponentials theorem, which is not formalised. Vacuous if Diaz's conjecture holds.
--
--   **Novelty.** The statement is a short consequence of the four exponentials theorem in transcendence degree one. Novelty is not asserted.
-- source:
--   Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.9, 25 September 2026 (GitHub release note-v1.9), Section 6, the paragraph after Corollary 6.8. Novelty is not asserted. Formal proof: Diaz modulus mission, 23 September 2026 (C. Perassi). Background: W. D. Brownawell, J. Number Theory 6 (1974); M. Waldschmidt, J. Number Theory 5 (1973).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem candidate_harmonic_not_log (u : ℂ) (hu : IsCandidate u) (p q : ℚ) (hp : p ≠ 0)
    (hq : q ≠ 0) :
    Transcendental ℚ (Complex.exp (u * conj u / ((p : ℂ) * u + (q : ℂ) * conj u))) := by sorry

end DiazModulus
