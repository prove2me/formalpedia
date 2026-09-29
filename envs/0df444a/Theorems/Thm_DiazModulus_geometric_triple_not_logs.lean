-- Prove2me | Theorems.Thm_DiazModulus_geometric_triple_not_logs
-- name    : DiazModulus.geometric_triple_not_logs
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T16:20:08.296444+00:00
-- url     : https://prove2.me/theorems/96e4d77b-1d33-4d55-a45f-28352c99c8f2
-- title:
--   No three logarithms of algebraic numbers in geometric progression in transcendence degree one
-- statement:
--   **Geometric progressions of logarithms.**
--
--   Let $w \neq 0$ and $z \notin \mathbb{Q}$ be complex numbers such that $\mathbb{Q}(w, z)$ has transcendence degree at most one. Then $w$, $wz$ and $wz^{2}$ are not all logarithms of algebraic numbers: at least one of
--
--   $$\mathrm{e}^{w}, \qquad \mathrm{e}^{wz}, \qquad \mathrm{e}^{wz^{2}}$$
--
--   is transcendental.
--
--   The matrix $\begin{pmatrix} w & wz \\ wz & wz^{2}\end{pmatrix}$ is the simplest $2\times2$ matrix with vanishing determinant whose entries are tied by a single ratio. This node is the corresponding instance of the four exponentials theorem in transcendence degree one, `DiazModulus.four_exponentials_trdeg_one`. With $w = i\pi$ and $z = -i\pi$ it gives `DiazModulus.exp_pi_sq_or_exp_i_pi_cube_transcendental`. With $w = z = \log\alpha$ it says that $\alpha^{\log\alpha}$ and $\alpha^{\log^{2}\alpha}$ are not both algebraic, for algebraic $\alpha > 0$, $\alpha \neq 1$.
--
--   **Formalization note.** The transcendence degree is that of `Algebra.adjoin ℚ {w, z}`, and $z \notin \mathbb{Q}$ is written `∀ q : ℚ, z ≠ q`.
--
--   **Novelty.** None: the statement is classical. It is Corollaire 7.4.3 of M. Waldschmidt, *Nombres transcendants*, Lecture Notes in Math. **402** (1974), p. 202: for $\ell \neq 0$ and $x$ algebraic over $\mathbb{Q}(\ell)$ and irrational, one of $e^{\ell}$, $e^{x\ell}$, $e^{x^{2}\ell}$ is transcendental. An equivalent form is Exercise 15.16(b)(ii) of Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups* (Springer 2000), whose hint points to G. Diaz, J. Théor. Nombres Bordeaux **9** (1997); it is on p. 241 there. The contribution of this node is the formal proof.
-- source:
--   Classical: M. Waldschmidt, Nombres transcendants, Lecture Notes in Math. 402, Springer, 1974, Corollaire 7.4.3, p. 202; M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, Exercise 15.16(b)(ii); G. Diaz, La conjecture des quatre exponentielles et les conjectures de D. Bertrand sur la fonction modulaire, J. Théor. Nombres Bordeaux 9 (1997), 229–245, p. 241. Formal proof: Diaz modulus mission, 23 September 2026 (C. Perassi).

import Mathlib

namespace DiazModulus

theorem geometric_triple_not_logs (w z : ℂ) (hw : w ≠ 0) (hz : ∀ q : ℚ, z ≠ (q : ℂ))
    (htr : Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({w, z} : Set ℂ)) ≤ 1) :
    ¬ (IsAlgebraic ℚ (Complex.exp w) ∧ IsAlgebraic ℚ (Complex.exp (w * z)) ∧
      IsAlgebraic ℚ (Complex.exp (w * z ^ 2))) := by sorry

end DiazModulus
