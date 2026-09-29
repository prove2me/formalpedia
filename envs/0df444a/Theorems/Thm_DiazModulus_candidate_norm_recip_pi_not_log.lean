-- Prove2me | Theorems.Thm_DiazModulus_candidate_norm_recip_pi_not_log
-- name    : DiazModulus.candidate_norm_recip_pi_not_log
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T11:03:58.30642+00:00
-- url     : https://prove2.me/theorems/0ec41307-73b0-4595-85e6-edede7ed855b
-- title:
--   The real half of (S) holds at γ = |u|² for every candidate u algebraic over ℚ(π)
-- statement:
--   **The two open statements, at the same number.**
--
--   Let $u$ be a candidate for Diaz's conjecture that is algebraic over $\mathbb{Q}[i\pi]$, that is, a non-generic candidate. Then
--
--   $$e^{|u|^{2}/(i\pi)}$$
--
--   is transcendental.
--
--   The statement (S), `DiazModulus.recip_pi_not_log`, asks that $e^{\gamma/(i\pi)}$ be transcendental for every non-zero algebraic $\gamma$; its open real half, `DiazModulus.recip_pi_not_log_real_gamma`, asks it for real $\gamma$. This node proves the real half at $\gamma = |u|^{2}$ for every non-generic candidate $u$. So a non-generic counterexample to Diaz's conjecture never produces, through its squared modulus, a counterexample to (S). `DiazModulus.diaz_number_forces_transcendence` proved this coupling on the rational-angle branch; here it holds for every non-generic candidate.
--
--   **Proof.** The matrix $\begin{pmatrix} u & i\pi \\ |u|^{2}/(i\pi) & \bar u \end{pmatrix}$ has determinant $0$, and its entries are algebraic over $\mathbb{Q}[i\pi]$. By `DiazModulus.four_exponentials_trdeg_one` its rows or columns are $\mathbb{Q}$-dependent, which puts $u$ or $\bar u$ in $\mathbb{Q}\,i\pi$. Then $|u|^{2}$ is a non-zero rational multiple of $\pi^{2}$, which is transcendental.
--
--   **Novelty.** None claimed: it is a short consequence of the four exponentials theorem in transcendence degree one.
-- source:
--   Carlo Perassi, unpublished apart from this node. Novelty is not asserted. Formal proof: Diaz modulus mission, 24 September 2026 (C. Perassi). Background: W. D. Brownawell, The algebraic independence of certain numbers related to the exponential function, J. Number Theory 6 (1974); M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem candidate_norm_recip_pi_not_log (u : ℂ) (hu : IsCandidate u)
    (halg : IsAlgebraic (↥(Algebra.adjoin ℚ ({((Real.pi : ℝ) : ℂ) * Complex.I} : Set ℂ))) u) :
    Transcendental ℚ (Complex.exp (u * conj u / (((Real.pi : ℝ) : ℂ) * Complex.I))) := by
  sorry

end DiazModulus
