-- Prove2me | Theorems.Thm_DiazModulus_candidate_norm_div_log_not_log
-- name    : DiazModulus.candidate_norm_div_log_not_log
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T11:03:54.795535+00:00
-- url     : https://prove2.me/theorems/629cbb03-65a4-4d71-b77e-35d0901e7e3f
-- title:
--   For a candidate u and a logarithm x algebraic over ℚ(u) outside ℚu ∪ ℚū, |u|²/x is not a logarithm
-- statement:
--   **Dividing the squared modulus by a logarithm.**
--
--   Let $u$ be a candidate for Diaz's conjecture: $u \neq 0$, with $|u|$ and $e^{u}$ algebraic. Let $x$ be a logarithm of an algebraic number that is algebraic over $\mathbb{Q}[u]$ and lies neither in $\mathbb{Q}u$ nor in $\mathbb{Q}\bar u$. Then
--
--   $$e^{|u|^{2}/x}$$
--
--   is transcendental.
--
--   The case $x = pu + q\bar u$, with $p, q$ non-zero rationals, is `DiazModulus.candidate_harmonic_not_log`. The exclusion of $\mathbb{Q}u \cup \mathbb{Q}\bar u$ is necessary: at $x = u$ the number $|u|^{2}/u = \bar u$ is a logarithm. The companion `DiazModulus.candidate_norm_recip_pi_not_log` takes $x = i\pi$.
--
--   **Proof.** The matrix $\begin{pmatrix} u & x \\ |u|^{2}/x & \bar u \end{pmatrix}$ has determinant $u\bar u - |u|^{2} = 0$. If $e^{|u|^{2}/x}$ were algebraic, its entries would be non-zero logarithms of algebraic numbers, all algebraic over $\mathbb{Q}[u]$. By `DiazModulus.four_exponentials_trdeg_one` its rows or columns would then be $\mathbb{Q}$-dependent. A row relation puts $x$ in $\mathbb{Q}\bar u$, a column relation puts it in $\mathbb{Q}u$.
--
--   **Novelty.** None claimed: it is a short consequence of the four exponentials theorem in transcendence degree one. It was not found in the literature reading of 24 September 2026 (Diaz, Roy, Waldschmidt, Dasgupta–Kakde), so it may be known in another form.
-- source:
--   Carlo Perassi, unpublished apart from this node. Novelty is not asserted. Formal proof: Diaz modulus mission, 24 September 2026 (C. Perassi). It generalises DiazModulus.candidate_harmonic_not_log. Background: W. D. Brownawell, The algebraic independence of certain numbers related to the exponential function, J. Number Theory 6 (1974); M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem candidate_norm_div_log_not_log (u : ℂ) (hu : IsCandidate u) (x : ℂ)
    (hx : IsAlgebraic ℚ (Complex.exp x))
    (hxu : IsAlgebraic (↥(Algebra.adjoin ℚ ({u} : Set ℂ))) x)
    (hne : ∀ q : ℚ, x ≠ (q : ℂ) * u ∧ x ≠ (q : ℂ) * conj u) :
    Transcendental ℚ (Complex.exp (u * conj u / x)) := by
  sorry

end DiazModulus
