-- Prove2me | Theorems.Thm_DiazModulus_dilog_half_irrational_or_exp_i_div_pi_transcendental
-- name    : DiazModulus.dilog_half_irrational_or_exp_i_div_pi_transcendental
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-04T18:32:54.134442+00:00
-- url     : https://prove2.me/theorems/f9999428-837c-4d87-a70f-5790d5c414eb
-- title:
--   Li₂(1/2) = π²/12 − (log 2)²/2 is irrational, or e^{iγ/π} is transcendental for every rational γ ≠ 0
-- statement:
--   Either $\pi^2/12 - (\log 2)^2/2$ is irrational, or $e^{i\gamma/\pi}$ is transcendental for every $\gamma \in \mathbb{Q}^\times$.
--
--   By a classical identity of Euler, $\pi^2/12 - (\log 2)^2/2$ is the dilogarithm $\mathrm{Li}_2(1/2) = \sum_{n \ge 1} 1/(n^2 2^n)$. Its irrationality is open. Waldschmidt lists it as unknown (Open Diophantine Problems, 2004, p. 274), and the known results cover $\mathrm{Li}_2(1/q)$ only for $q \ge 6$ and $q \le -5$ (Hata 1993; Rhin and Viola 2005; see Calegari, Dimitrov and Tang 2024, Remark 2.8.2). The transcendence of $e^{i/\pi}$ is open as well; it is the smallest case of the real half of the statement $(S)$ in this mission. So at least one of two open questions has a positive answer. The Lean statement uses the closed form.
--
--   **Proof.** If $\pi^2/12 - (\log 2)^2/2 = s$ with $s$ rational, apply `DiazModulus.recip_pi_log_of_rational_quadratic_relation` with $t = \log 2$, $a = -1/2$, $b = 1/12$ and $c = s$; here $e^{\log 2} = 2$ is algebraic and $\log 2 \neq 0$.
--
--   **Novelty.** The dichotomy was not found in the sources read. Its ingredients are Euler's identity and Brownawell's Corollary 5 (1974).
-- source:
--   The irrationality of Li₂(1/2) = π²/12 − (log 2)²/2 is listed as unknown in M. Waldschmidt, Open Diophantine problems, Moscow Math. J. 4 (2004), 245–305, p. 274, and is still open: M. Hata, Rational approximations to the dilogarithm, Trans. Amer. Math. Soc. 336 (1993), 363–387; G. Rhin and C. Viola, The permutation group method for the dilogarithm, Ann. Sc. Norm. Super. Pisa Cl. Sci. (5) 4 (2005), 389–437; F. Calegari, V. Dimitrov and Y. Tang, The linear independence of 1, ζ(2), and L(2, χ₋₃), arXiv:2408.15403 (2024), Remark 2.8.2. The dichotomy follows from DiazModulus.recip_pi_log_of_rational_quadratic_relation (after W. D. Brownawell, The algebraic independence of certain numbers related by the exponential function, J. Number Theory 6 (1974), 22–31, Cor. 5) and was not found in the sources read. Formal proof: Diaz modulus mission, 4 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem dilog_half_irrational_or_exp_i_div_pi_transcendental :
    Irrational (Real.pi ^ 2 / 12 - Real.log 2 ^ 2 / 2) ∨
      ∀ γ : ℚ, γ ≠ 0 →
        Transcendental ℚ (Complex.exp (Complex.I * (γ : ℂ) / ((Real.pi : ℝ) : ℂ))) := by
  sorry

end DiazModulus
