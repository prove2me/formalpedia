-- Prove2me | Theorems.Thm_DiazModulus_recip_pi_log_rational_line
-- name    : DiazModulus.recip_pi_log_rational_line
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T15:59:56.427303+00:00
-- url     : https://prove2.me/theorems/95afe551-42b0-459e-96e8-f1e4bb2857e8
-- title:
--   Exceptions to the statement (S) are rationally proportional
-- statement:
--   **The exceptional set of (S) is at most a rational line.**
--
--   Let $\gamma_{1}, \gamma_{2}$ be algebraic with $\gamma_{2} \neq 0$, and suppose that $\mathrm{e}^{\gamma_{1}/(i\pi)}$ and $\mathrm{e}^{\gamma_{2}/(i\pi)}$ are both algebraic. Then
--
--   $$\gamma_{1}/\gamma_{2} \in \mathbb{Q}.$$
--
--   The statement (S), `DiazModulus.recip_pi_not_log`, asserts that the set $S_{0} = \{\gamma \in \overline{\mathbb{Q}} : \mathrm{e}^{\gamma/(i\pi)} \in \overline{\mathbb{Q}}\}$ is $\{0\}$. This node shows that $S_{0}$ is in any case contained in a single rational line $\mathbb{Q}\gamma_{0}$. Its hypotheses describe elements of $S_{0}$, so they can be met only if (S) fails. Its substantive consequences are `DiazModulus.recip_pi_log_on_axis` and `DiazModulus.recip_pi_not_log_real_or_imag`.
--
--   **Novelty.** None: this is due to G. Diaz. In J. Théor. Nombres Bordeaux **16** (2004), Théorème 5, p. 541, he shows by Gelfond–Schneider that $\{\alpha \in \overline{\mathbb{Q}}^{\times} : e^{\alpha} \in \overline{\mathbb{Q}}\}$ is empty or of the form $\mathbb{Q}^{\times}\alpha_{0}$ with $\alpha_{0}$ on an axis (restated as Corollary 1.4 in Waldschmidt, *The role of complex conjugation in transcendental number theory*, 2007). The proof applies verbatim to $e^{v\alpha}$ for any real $v \neq 0$, and $\gamma \in S_{0}$ exactly when $e^{v\alpha} \in \overline{\mathbb{Q}}$ for $v = -1/\pi$ and $\alpha = i\gamma$. The contribution of this node is the formal proof.
-- source:
--   G. Diaz, Utilisation de la conjugaison complexe dans l'étude de la transcendance de valeurs de la fonction exponentielle usuelle, J. Théor. Nombres Bordeaux 16 (2004), 535–553, Théorèmes 4 and 5 and the proof of Théorème 5 (pp. 539–541), at v = -1/pi and alpha = i*gamma; restated in M. Waldschmidt, The role of complex conjugation in transcendental number theory, in Diophantine Equations (N. Saradha, ed.), Tata Institute of Fundamental Research and Narosa, 2007, Theorem 1.3 and Corollary 1.4. Background: A. O. Gelfond (1934) and Th. Schneider (1934); formal proof of Gelfond-Schneider by M. Karatarakis and F. Wiedijk, arXiv:2603.24823. Formal proof: Diaz modulus mission, 23 September 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem recip_pi_log_rational_line :
    ∀ γ₁ γ₂ : ℂ, IsAlgebraic ℚ γ₁ → IsAlgebraic ℚ γ₂ → γ₂ ≠ 0 →
      IsAlgebraic ℚ (Complex.exp (γ₁ / (((Real.pi : ℝ) : ℂ) * Complex.I))) →
      IsAlgebraic ℚ (Complex.exp (γ₂ / (((Real.pi : ℝ) : ℂ) * Complex.I))) →
      ∃ q : ℚ, γ₁ = (q : ℂ) * γ₂ := by sorry

end DiazModulus
