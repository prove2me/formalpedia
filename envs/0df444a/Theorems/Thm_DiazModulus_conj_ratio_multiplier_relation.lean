-- Prove2me | Theorems.Thm_DiazModulus_conj_ratio_multiplier_relation
-- name    : DiazModulus.conj_ratio_multiplier_relation
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T18:33:49.510131+00:00
-- url     : https://prove2.me/theorems/903b66a1-9aa8-45a0-8e79-8857a789f070
-- title:
--   What the ratio u/ū multiplies into ℒ forces a rational relation
-- statement:
--   **The involution lemma.**
--
--   Let $u$ be a logarithm of an algebraic number lying on neither axis, and let $w$ be a logarithm of an algebraic number such that $uw/\bar u$ is also one. Then there are rationals $a, b, c$, not all zero, with
--
--   $$a\,|u|^{2} + b\,uw + c\,\overline{uw} = 0 .$$
--
--   Equivalently, $uw$ is real or $\operatorname{Re}(uw) \in \mathbb{Q}\,|u|^{2}$. The single hypothesis $e^{uw/\bar u} \in \overline{\mathbb{Q}}$ supplies two logarithms, $w$ and $\overline{(u/\bar u)\,w}$, next to $\bar u$. This is how the six exponentials theorem gets past the dimension count of a single candidate. It is the common step of `DiazModulus.candidate_quotient_rigid` and `DiazModulus.candidate_neg_one_pow_ratio`.
--
--   **Novelty.** None: this is the $\mathbb{Q}$-linear form of Corollaire 4(4) of G. Diaz, J. Théor. Nombres Bordeaux **19** (2007), p. 383, which gives the same conclusion over $\overline{\mathbb{Q}}$ and $\widetilde{\mathcal{L}}$ from Roy's strong six exponentials theorem; Diaz notes (p. 380) that the classical six exponentials theorem gives the $\mathbb{Q}$-linear forms in the same way. The contribution of this node is the formal proof.
-- source:
--   The six exponentials theorem (S. Lang, 1966; K. Ramachandra, 1968); the statement is the Q-linear form of G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, Corollaire 4(4). Formal proof: Diaz modulus mission, 23 September 2026 (C. Perassi).

import Mathlib

open ComplexConjugate

namespace DiazModulus

theorem conj_ratio_multiplier_relation (u w : ℂ) (hre : u.re ≠ 0) (him : u.im ≠ 0)
    (heu : IsAlgebraic ℚ (Complex.exp u)) (hew : IsAlgebraic ℚ (Complex.exp w))
    (hsw : IsAlgebraic ℚ (Complex.exp (u * w / conj u))) :
    ∃ a b c : ℚ, ¬(a = 0 ∧ b = 0 ∧ c = 0) ∧
      (a : ℂ) * (u * conj u) + (b : ℂ) * (u * w) + (c : ℂ) * conj (u * w) = 0 := by sorry

end DiazModulus
