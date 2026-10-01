-- Prove2me | Theorems.Thm_DiazModulus_algebraic_modulus_log_multiplier_rational
-- name    : DiazModulus.algebraic_modulus_log_multiplier_rational
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-01T08:52:41.199135+00:00
-- url     : https://prove2.me/theorems/6ffe26c9-fec5-4a4b-b75b-7a6e947b0cbb
-- title:
--   If λ ∈ ℒ∖{0}, u ∈ ℒ̃, |u| is algebraic and e^{uλ} is algebraic, then u or uλ/λ̄ is rational (strong six exponentials and Baker)
-- statement:
--   Here $\mathcal{L}$ is the set of logarithms of algebraic numbers, and $\widetilde{\mathcal{L}}$ is the $\overline{\mathbb{Q}}$-vector space spanned by $1$ and $\mathcal{L}$. Roy's strong six exponentials theorem is carried as the hypothesis `hSSE`: if $x_1, x_2$ are $\overline{\mathbb{Q}}$-linearly independent and so are $y_1, y_2, y_3$, then one of the six products $x_iy_j$ is not in $\widetilde{\mathcal{L}}$. Baker's theorem is carried as the hypothesis `hB`, in its two-logarithm inhomogeneous form, as in `DiazModulus.candidate_one_log_saturation`.
--
--   Let $\lambda \in \mathcal{L}$, $\lambda \neq 0$, and $u \in \widetilde{\mathcal{L}}$ with $|u|$ algebraic. If $e^{u\lambda}$ is algebraic, then $u \in \mathbb{Q}$ or $u\lambda/\bar\lambda \in \mathbb{Q}$.
--
--   For arbitrary complex $u$ this is an open problem listed in Waldschmidt's *Diophantine Approximation on Linear Algebraic Groups* (2000), p. 399, as a consequence of the strong four exponentials conjecture pointed out by G. Diaz (1997). This node proves the case $u \in \widetilde{\mathcal{L}}$.
--
--   **Proof.** If $u$ is algebraic, Gelfond–Schneider (`Schanuel.gelfond_schneider`) gives $u \in \mathbb{Q}$. Otherwise apply the strong six exponentials theorem to $x = (1, u)$ and $y = (\lambda, \overline{u\lambda}, 1)$. The six products are $\lambda$, $\overline{u\lambda}$, $1$, $u\lambda$, $|u|^2\bar\lambda$ and $u$, all in $\widetilde{\mathcal{L}}$. As $x$ is linearly independent over $\overline{\mathbb{Q}}$, $y$ is not: $a\lambda + b\,\overline{u\lambda} + c = 0$. Baker's theorem makes $\lambda$ and $\overline{u\lambda}$ linearly dependent over $\mathbb{Q}$, so $\overline{u\lambda} = r\lambda$ with $r \in \mathbb{Q}$; conjugating, $u\lambda/\bar\lambda = r$.
--
--   Baker's theorem is needed: the strong six exponentials theorem alone gives only $\overline{u\lambda} \in \overline{\mathbb{Q}} + \overline{\mathbb{Q}}\lambda$.
--
--   **Novelty.** The statement is Waldschmidt's (2000, p. 399), following Diaz (1997). The derivation of its case $u \in \widetilde{\mathcal{L}}$ from the strong six exponentials theorem and Baker's theorem was not found in the sources read: Diaz (1997, §§III–IV; 2004; 2007, §2), Waldschmidt's *Variations* (§2) and *The role of complex conjugation* (§5), and *Diophantine Approximation on Linear Algebraic Groups*, §11.6.
-- source:
--   The statement: M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, p. 399, following G. Diaz, La conjecture des quatre exponentielles et les conjectures de D. Bertrand sur la fonction modulaire, J. Théor. Nombres Bordeaux 9 (1997), 229–245. The case u ∈ ℒ̃ under the strong six exponentials theorem (D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47, Corollary 2 of §4) and Baker's theorem: Formal proof: Diaz modulus mission, 1 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

/-- If `l ∈ ℒ ∖ {0}`, `u ∈ ℒ̃`, `|u|` is algebraic and `e^{ul}` is algebraic, then `u ∈ ℚ` or `ul/l̄ ∈ ℚ`,
assuming Roy's strong six exponentials theorem `hSSE` and Baker's theorem `hB`. -/
theorem algebraic_modulus_log_multiplier_rational
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde))
    (hB : ∀ x y a b : ℂ,
      IsAlgebraic ℚ (Complex.exp x) → IsAlgebraic ℚ (Complex.exp y) →
      (∀ p q : ℚ, (p : ℂ) * x + (q : ℂ) * y = 0 → p = 0 ∧ q = 0) →
      IsAlgebraic ℚ a → IsAlgebraic ℚ b → ¬(a = 0 ∧ b = 0) →
      Transcendental ℚ (a * x + b * y))
    {l u : ℂ} (hl : l ∈ LogAlg) (hl0 : l ≠ 0) (hu : u ∈ LogAlgTilde)
    (hnorm : IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ))
    (hexp : IsAlgebraic ℚ (Complex.exp (u * l))) :
    (∃ q : ℚ, u = (q : ℂ)) ∨ (∃ q : ℚ, u * l / conj l = (q : ℂ)) := by
  sorry

end DiazModulus
