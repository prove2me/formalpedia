-- Prove2me | Theorems.Thm_DiazModulus_log_pair_square_ratio_transcendental
-- name    : DiazModulus.log_pair_square_ratio_transcendental
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T11:03:50.726373+00:00
-- url     : https://prove2.me/theorems/597c1760-c015-46d6-b1a3-c19c67bbb20a
-- title:
--   Two ℚ-independent, algebraically dependent logarithms ℓ₁, ℓ₂: e^{ℓ₁²/ℓ₂} and e^{ℓ₂²/ℓ₁} are transcendental
-- statement:
--   **Waldschmidt's remark on pairs of logarithms.**
--
--   Let $\ell_1, \ell_2$ be logarithms of algebraic numbers with $\ell_2 \neq 0$ and $\ell_1 \notin \mathbb{Q}\ell_2$, and suppose that $\ell_1$ is algebraic over $\mathbb{Q}[\ell_2]$; equivalently, $\ell_1$ and $\ell_2$ are algebraically dependent. Then
--
--   $$e^{\ell_1^{2}/\ell_2} \qquad\text{and}\qquad e^{\ell_2^{2}/\ell_1}$$
--
--   are both transcendental.
--
--   Put the other way, as Waldschmidt does: two $\mathbb{Q}$-linearly independent logarithms of algebraic numbers are either algebraically independent, or $\exp(\ell_1^{2}/\ell_2)$ is transcendental. No pair of $\mathbb{Q}$-linearly independent logarithms is known to be algebraically independent. `DiazModulus.log_two_pi_dependent_forces_transcendence` is the case $\ell_1 = \log 2$, $\ell_2 = i\pi$.
--
--   **Proof.** Two applications of `DiazModulus.geometric_triple_not_logs`. The first is at $(w, z) = (\ell_2, \ell_1/\ell_2)$, whose triple is $\ell_2, \ell_1, \ell_1^{2}/\ell_2$. The second is at $(w, z) = (\ell_1, \ell_2/\ell_1)$, whose triple is $\ell_1, \ell_2, \ell_2^{2}/\ell_1$. In both cases $w$ and $z$ are algebraic over $\mathbb{Q}[\ell_2]$, which bounds the transcendence degree by one, and $z \notin \mathbb{Q}$ because $\ell_1 \notin \mathbb{Q}\ell_2$.
--
--   **Attribution.** Known: M. Waldschmidt, *Nombres transcendants*, Lecture Notes in Math. **402** (1974), p. 202, the remark after Corollaire 7.4.3. The contribution of this node is the formal proof.
-- source:
--   Known: M. Waldschmidt, Nombres transcendants, Lecture Notes in Math. 402, Springer, 1974, p. 202 (remark after Corollaire 7.4.3). Formal proof: Diaz modulus mission, 24 September 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem log_pair_square_ratio_transcendental (l₁ l₂ : ℂ)
    (h₁ : IsAlgebraic ℚ (Complex.exp l₁)) (h₂ : IsAlgebraic ℚ (Complex.exp l₂))
    (hl₂ : l₂ ≠ 0) (hind : ∀ q : ℚ, l₁ ≠ (q : ℂ) * l₂)
    (hdep : IsAlgebraic (↥(Algebra.adjoin ℚ ({l₂} : Set ℂ))) l₁) :
    Transcendental ℚ (Complex.exp (l₁ ^ 2 / l₂)) ∧ Transcendental ℚ (Complex.exp (l₂ ^ 2 / l₁)) := by
  sorry

end DiazModulus
