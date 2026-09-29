-- Prove2me | Theorems.Thm_DiazModulus_recip_pi_log_on_axis
-- name    : DiazModulus.recip_pi_log_on_axis
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T16:00:00.171479+00:00
-- url     : https://prove2.me/theorems/6a04db18-2ccd-4c59-897c-83c9d8a8a384
-- title:
--   An exception to the statement (S) is real or purely imaginary
-- statement:
--   **Exceptions to (S) lie on an axis.**
--
--   Let $\gamma$ be algebraic with $\mathrm{e}^{\gamma/(i\pi)}$ algebraic. Then
--
--   $$\operatorname{Re}\gamma = 0 \qquad\text{or}\qquad \operatorname{Im}\gamma = 0 .$$
--
--   With `DiazModulus.recip_pi_log_rational_line`, the exceptional set of (S), $S_{0} = \{\gamma \in \overline{\mathbb{Q}} : \mathrm{e}^{\gamma/(i\pi)} \in \overline{\mathbb{Q}}\}$, is either $\{0\}$ or a rational line lying on the real or on the imaginary axis. The known split of (S) into a real half and an imaginary half is therefore a partition of $S_{0}$, not merely a decomposition of its elements.
--
--   **Novelty.** None: this is Théorème 4 of G. Diaz, J. Théor. Nombres Bordeaux **16** (2004), p. 539 (restated as Theorem 1.3 in Waldschmidt, *The role of complex conjugation in transcendental number theory*, 2007): for algebraic $\alpha$ on neither axis and real $v \neq 0$, $e^{v\alpha}$ is transcendental, by Gelfond–Schneider applied to $\alpha$ and $\bar\alpha$. Here $v = -1/\pi$ and $\alpha = i\gamma$. The contribution of this node is the formal proof.
-- source:
--   G. Diaz, Utilisation de la conjugaison complexe dans l'étude de la transcendance de valeurs de la fonction exponentielle usuelle, J. Théor. Nombres Bordeaux 16 (2004), 535–553, Théorèmes 4 and 5 and the proof of Théorème 5 (pp. 539–541), at v = -1/pi and alpha = i*gamma; restated in M. Waldschmidt, The role of complex conjugation in transcendental number theory, in Diophantine Equations (N. Saradha, ed.), Tata Institute of Fundamental Research and Narosa, 2007, Theorem 1.3 and Corollary 1.4. Background: A. O. Gelfond (1934) and Th. Schneider (1934); formal proof of Gelfond-Schneider by M. Karatarakis and F. Wiedijk, arXiv:2603.24823. Formal proof: Diaz modulus mission, 23 September 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem recip_pi_log_on_axis :
    ∀ γ : ℂ, IsAlgebraic ℚ γ →
      IsAlgebraic ℚ (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))) →
      γ.re = 0 ∨ γ.im = 0 := by sorry

end DiazModulus
