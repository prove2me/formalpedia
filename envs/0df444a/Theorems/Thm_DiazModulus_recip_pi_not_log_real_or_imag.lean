-- Prove2me | Theorems.Thm_DiazModulus_recip_pi_not_log_real_or_imag
-- name    : DiazModulus.recip_pi_not_log_real_or_imag
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T16:00:07.72346+00:00
-- url     : https://prove2.me/theorems/a7246ee7-442e-45cd-bf46-09d6f4a1cef4
-- title:
--   At least one of the two halves of the statement (S) holds
-- statement:
--   **At least one half of (S) holds.**
--
--   Either for every non-zero real algebraic $\gamma$ the number $\mathrm{e}^{\gamma/(i\pi)}$ is transcendental, or for every non-zero purely imaginary algebraic $\gamma$ it is:
--
--   $$\bigl(\forall \gamma \in \overline{\mathbb{Q}} \cap \mathbb{R}^{\times},\ \mathrm{e}^{\gamma/(i\pi)} \notin \overline{\mathbb{Q}}\bigr) \ \vee\ \bigl(\forall \gamma \in \overline{\mathbb{Q}} \cap i\mathbb{R}^{\times},\ \mathrm{e}^{\gamma/(i\pi)} \notin \overline{\mathbb{Q}}\bigr).$$
--
--   The two halves are the open nodes `DiazModulus.recip_pi_not_log_real_gamma` and `DiazModulus.recip_pi_not_log_imag_gamma`. For real $\gamma$ the first says that $\mathrm{e}^{-i\gamma/\pi}$, a point of the unit circle, is transcendental. For $\gamma = i\beta$ the second says that $\mathrm{e}^{\beta/\pi}$ is transcendental. Neither is known. This node proves their disjunction: whatever the truth of (S), it can fail in at most one of the two directions. Unlike the two preceding nodes, it has no hypotheses.
--
--   **Novelty.** None: this is the clause "$\alpha_{0} \in \mathbb{R} \cup i\mathbb{R}$" of Théorème 5 of G. Diaz, J. Théor. Nombres Bordeaux **16** (2004), p. 541, whose proof applies verbatim to $e^{v\alpha}$ with $v = -1/\pi$ (see `DiazModulus.recip_pi_log_rational_line`). The contribution of this node is the formal proof.
-- source:
--   G. Diaz, Utilisation de la conjugaison complexe dans l'étude de la transcendance de valeurs de la fonction exponentielle usuelle, J. Théor. Nombres Bordeaux 16 (2004), 535–553, Théorèmes 4 and 5 and the proof of Théorème 5 (pp. 539–541), at v = -1/pi and alpha = i*gamma; restated in M. Waldschmidt, The role of complex conjugation in transcendental number theory, in Diophantine Equations (N. Saradha, ed.), Tata Institute of Fundamental Research and Narosa, 2007, Theorem 1.3 and Corollary 1.4. Background: A. O. Gelfond (1934) and Th. Schneider (1934); formal proof of Gelfond-Schneider by M. Karatarakis and F. Wiedijk, arXiv:2603.24823. Formal proof: Diaz modulus mission, 23 September 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem recip_pi_not_log_real_or_imag :
    (∀ γ : ℂ, IsAlgebraic ℚ γ → γ ≠ 0 → γ.im = 0 →
      ¬ IsAlgebraic ℚ (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I)))) ∨
    (∀ γ : ℂ, IsAlgebraic ℚ γ → γ ≠ 0 → γ.re = 0 →
      ¬ IsAlgebraic ℚ (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I)))) := by sorry

end DiazModulus
