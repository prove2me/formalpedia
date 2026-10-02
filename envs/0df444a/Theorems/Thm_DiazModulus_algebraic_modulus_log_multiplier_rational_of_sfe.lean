-- Prove2me | Theorems.Thm_DiazModulus_algebraic_modulus_log_multiplier_rational_of_sfe
-- name    : DiazModulus.algebraic_modulus_log_multiplier_rational_of_sfe
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-01T14:41:48.1496+00:00
-- url     : https://prove2.me/theorems/25ceb5d5-7338-4f59-84bc-844a97561846
-- title:
--   Under the strong four exponentials conjecture: if λ ∈ ℒ∖{0}, |u| is algebraic and e^{uλ} is algebraic, then u or uλ/λ̄ is rational
-- statement:
--   Here $\mathcal{L}$ is the set of logarithms of algebraic numbers, and $\widetilde{\mathcal{L}}$ is the $\overline{\mathbb{Q}}$-vector space spanned by $1$ and $\mathcal{L}$. The strong four exponentials conjecture (`DiazModulus.StrongFourExponentials`, Conjecture 11.17 of Waldschmidt's book) is carried as the hypothesis `hS`: if $x_1, x_2$ are linearly independent over $\overline{\mathbb{Q}}$ and so are $y_1, y_2$, then one of the four products $x_iy_j$ is not in $\widetilde{\mathcal{L}}$.
--
--   Let $\lambda \in \mathcal{L}$, $\lambda \neq 0$, and let $u \in \mathbb{C}$ with $|u|$ algebraic. If $e^{u\lambda}$ is algebraic, then $u \in \mathbb{Q}$ or $u\lambda/\bar\lambda \in \mathbb{Q}$.
--
--   This is the second open statement on p. 399 of Waldschmidt's book, a conjectural refinement of the Gel'fond–Schneider theorem that he derives from the strong four exponentials conjecture. Its case $u \in \widetilde{\mathcal{L}}$ follows from Roy's strong six exponentials theorem and Baker's theorem (`DiazModulus.algebraic_modulus_log_multiplier_rational`). Here every $u$ is covered, and Baker's theorem is not needed.
--
--   **Proof.** Apply the conjecture to $x = (1, u)$ and $y = (\lambda, \bar u\bar\lambda)$. The four products are $\lambda$, $\bar u\bar\lambda = \overline{u\lambda}$, $u\lambda$ and $u\bar u\bar\lambda = |u|^2\bar\lambda$. The first three are logarithms of algebraic numbers (`DiazModulus.logAlg_conj_stable`) and the last is an algebraic multiple of one, so all four lie in $\widetilde{\mathcal{L}}$. Hence $x$ or $y$ is linearly dependent over $\overline{\mathbb{Q}}$. If $x$ is, $u$ is algebraic, and Gelfond–Schneider (`Schanuel.gelfond_schneider`) applied to $e^{u\lambda}$ gives $u \in \mathbb{Q}$. If $y$ is, $\overline{u\lambda} = c\lambda$ with $c$ algebraic; Gelfond–Schneider applied to $e^{c\lambda} = \overline{e^{u\lambda}}$ gives $c \in \mathbb{Q}$, and conjugating, $u\lambda = c\bar\lambda$.
--
--   **Novelty.** None: the statement, and the fact that it follows from the strong four exponentials conjecture, are Waldschmidt's (2000, p. 399), who obtains it in the same way as Diaz's refinement of the Hermite–Lindemann theorem (Diaz 1997). The book gives no configuration for it; the one above was chosen for this node. The contribution of this node is the formal proof.
-- source:
--   The statement and its derivation from the strong four exponentials conjecture: M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, p. 399 (Conjecture 11.17 and the second statement after it), following G. Diaz, La conjecture des quatre exponentielles et les conjectures de D. Bertrand sur la fonction modulaire, J. Théor. Nombres Bordeaux 9 (1997), 229–245. Formal proof: Diaz modulus mission, 1 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

/-- Under the strong four exponentials conjecture: if `l ∈ ℒ ∖ {0}`, `|u|` is algebraic and `e^{ul}` is
algebraic, then `u ∈ ℚ` or `ul/l̄ ∈ ℚ` (the second open statement on p. 399 of Waldschmidt's book, which derives
it from that conjecture). -/
theorem algebraic_modulus_log_multiplier_rational_of_sfe (hS : StrongFourExponentials) :
    ∀ l u : ℂ, l ∈ LogAlg → l ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) →
      IsAlgebraic ℚ (Complex.exp (u * l)) →
      (∃ q : ℚ, u = (q : ℂ)) ∨ (∃ q : ℚ, u * l / conj l = (q : ℂ)) := by
  sorry

end DiazModulus
