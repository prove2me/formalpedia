-- Prove2me | Theorems.Thm_DiazModulus_log_square_duality
-- name    : DiazModulus.log_square_duality
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T18:24:09.645082+00:00
-- url     : https://prove2.me/theorems/1a14baed-d58b-41ec-aa92-f9007912d58a
-- title:
--   For ℚ-independent logarithms λ, μ, e^{λ²/μ} or e^{μ²/λ} is transcendental
-- statement:
--   **A six exponentials duality.**
--
--   Let $\lambda, \mu$ be logarithms of algebraic numbers that are linearly independent over $\mathbb{Q}$. Then at least one of
--
--   $$e^{\lambda^{2}/\mu} \qquad\text{and}\qquad e^{\mu^{2}/\lambda}$$
--
--   is transcendental.
--
--   Equivalently, no geometric progression $w/z, w, wz, wz^{2}$ of logarithms has a ratio $z$ of degree greater than two over $\mathbb{Q}$. Unlike `DiazModulus.geometric_triple_not_logs`, it needs no transcendence-degree hypothesis. Instances: `DiazModulus.two_pow_log_three_or_three_pow_log_two`. With $\lambda = \log 2$ and $\mu = i\pi$: one of $2^{i\log 2/\pi}$ and $e^{\pi^{2}/\log 2}$ is transcendental.
--
--   **Novelty.** None: this is the $\mathbb{Q}$-linear form of Corollaire 4(3) of G. Diaz, J. Théor. Nombres Bordeaux **19** (2007), p. 383, which from Roy's strong six exponentials theorem gives $\{\lambda^{2}/\mu,\ \mu^{2}/\lambda\} \not\subset \widetilde{\mathcal{L}}$ for $\overline{\mathbb{Q}}$-linearly independent $\lambda, \mu \in \widetilde{\mathcal{L}}$. The contribution of this node is the formal proof.
-- source:
--   The six exponentials theorem (Lang, Ramachandra) and the Gelfond-Schneider theorem (1934); the statement is the Q-linear form of G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, Corollaire 4(3). Formal proof: Diaz modulus mission, 23 September 2026 (C. Perassi).

import Mathlib

namespace DiazModulus

theorem log_square_duality (l m : ℂ) (hl : IsAlgebraic ℚ (Complex.exp l))
    (hm : IsAlgebraic ℚ (Complex.exp m)) (hind : LinearIndependent ℚ ![l, m]) :
    Transcendental ℚ (Complex.exp (l ^ 2 / m)) ∨ Transcendental ℚ (Complex.exp (m ^ 2 / l)) := by sorry

end DiazModulus
