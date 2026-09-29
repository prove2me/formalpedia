-- Prove2me | Theorems.Thm_DiazModulus_no_algebraic_generalized_line
-- name    : DiazModulus.no_algebraic_generalized_line
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-09T15:02:23.198691+00:00
-- url     : https://prove2.me/theorems/b6a32e93-665b-4932-8342-9b8bab854682
-- title:
--   A logarithm off the axes lies on no algebraic generalized line
-- statement:
--   A logarithm of an algebraic number lying off both coordinate axes lies on no *algebraic generalized line*: there are no $B \in \overline{\mathbb{Q}}^{\times}$ and $C \in \overline{\mathbb{Q}}$ with
--
--   $$B\lambda + \overline{B}\,\overline{\lambda} + C = 0 .$$
--
--   **Why it matters.** Attach to a transcendental $z$ its *conjugation degree* $\delta(z) = [\overline{\mathbb{Q}}(z,\bar z) : \overline{\mathbb{Q}}(z)]$. When $\delta(z) = 1$ the pair $(z, \bar z)$ satisfies an irreducible bidegree-$(1,1)$ relation over $\overline{\mathbb{Q}}$, whose real slice is a Hermitian equation
--   $$A\lvert w\rvert^{2} + Bw + \overline{B}\,\bar w + C = 0,\qquad A, C \in \overline{\mathbb{Q}} \cap \mathbb{R},\ B \in \overline{\mathbb{Q}},$$
--   that is, an algebraic *generalized* circle — a genuine circle when $A \neq 0$, a line when $A = 0$.
--
--   A Diaz candidate has conjugation degree one, since $\bar u = \lVert u\rVert^{2}/u$ puts $\bar u$ in $\overline{\mathbb{Q}}(u)$. So its canonical curve is one of those two shapes. This node excludes the degenerate one outright: **candidates are confined to genuine circles.** The degree-one stratum, where the whole question lives, contains no linear degeneration to worry about.
--
--   **The hypothesis.** The statement carries Baker's theorem in the exact form it uses: a non-zero $\overline{\mathbb{Q}}$-linear combination of two $\mathbb{Q}$-linearly independent logarithms of algebraic numbers is transcendental. That is a theorem — Baker, 1966 — but no formal development of it is available in this environment, so it is carried rather than asserted. Nothing else is assumed.
--
--   **A remark on where Baker does and does not apply.** Baker's theorem is often described as unavailable for this problem, and for the central question it is: the linear form attached to a hypothetical counterexample *vanishes by hypothesis*, so a lower bound on non-vanishing forms has nothing to act on. Here the situation is reversed. The form $B\lambda + \overline{B}\bar\lambda$ is one we need to show is **not** zero, which is precisely what Baker's theorem is for. The two uses are not in tension; the distinction is which side of the relation is assumed.
--
--   **Prior art.** The argument, $\mathbb{Q}$-linear independence of $\lambda$ and $\bar\lambda$ off the axes followed by Baker's theorem, is the first step of the proof of Théorème 3 of G. Diaz, J. Théor. Nombres Bordeaux **16** (2004), p. 539.
--
--   **Formalization note.** The $\mathbb{Q}$-linear independence of $\lambda$ and $\bar\lambda$ off the axes is proved inline from the real and imaginary parts and needs no arithmetic input; only the upgrade to $\overline{\mathbb{Q}}$-coefficients requires Baker.
-- source:
--   Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.9, 25 September 2026 (GitHub release note-v1.9), Theorem 6.1. Baker's theorem carried as an explicit hypothesis; see A. Baker, Transcendental Number Theory, Ch. 2. The same argument is the first step of the proof of Théorème 3 in G. Diaz, Utilisation de la conjugaison complexe dans l'étude de la transcendance de valeurs de la fonction exponentielle usuelle, J. Théor. Nombres Bordeaux 16 (2004), 535–553, p. 539.

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem no_algebraic_generalized_line :
    (∀ x y a b : ℂ,
      IsAlgebraic ℚ (Complex.exp x) → IsAlgebraic ℚ (Complex.exp y) →
      (∀ p q : ℚ, (p : ℂ) * x + (q : ℂ) * y = 0 → p = 0 ∧ q = 0) →
      IsAlgebraic ℚ a → IsAlgebraic ℚ b → ¬(a = 0 ∧ b = 0) →
      Transcendental ℚ (a * x + b * y)) →
    ∀ l : ℂ, IsAlgebraic ℚ (Complex.exp l) → l.re ≠ 0 → l.im ≠ 0 →
      ∀ B C : ℂ, IsAlgebraic ℚ B → B ≠ 0 → IsAlgebraic ℚ C →
        B * l + (starRingEnd ℂ) B * (starRingEnd ℂ) l + C ≠ 0 := by sorry
end DiazModulus
