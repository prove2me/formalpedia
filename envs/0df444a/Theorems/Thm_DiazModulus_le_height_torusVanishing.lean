-- Prove2me | Theorems.Thm_DiazModulus_le_height_torusVanishing
-- name    : DiazModulus.le_height_torusVanishing
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-30T09:52:28.704174+00:00
-- url     : https://prove2.me/theorems/43eded3b-1373-4af4-8ea8-9c70592c6c7c
-- title:
--   The ideal of the torus points $(x, y, y^{-1})$ in $\mathbb{C}[X, Y, Z]$ has height at least $|A_1|$
-- statement:
--   Let $A_0, A_1$ be finite types and $R = \mathbb{C}[X, Y, Z]$ the polynomial ring `MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ` in the variables $X_h$ ($h \in A_0$), $Y_i$ and $Z_i$ ($i \in A_1$), and $J_0 = (Y_iZ_i - 1)_{i \in A_1}$ its torus ideal (`torusIdeal`). The ideal of the polynomials vanishing at every point $(x, y, y^{-1})$ (`torusPoint x y`), $x \in \mathbb{C}^{A_0}$, $y \in (\mathbb{C}^\times)^{A_1}$, has height at least $|A_1|$. Krull dimensions take values in $\{-\infty\} \cup \mathbb{N} \cup \{\infty\}$ and heights in $\mathbb{N} \cup \{\infty\}$. `torusPoint` is that of the published Definition `DiazHilbertBox` (module `Definitions.Def_DiazHilbertBox`).
--
--   **Proof.** A chain of $|A_1| + 1$ primes below that ideal: the $k$-th member is the ideal of the image of the analytic map setting $(Y_i, Z_i) = (e^{u_i}, e^{-u_i})$ for the indices numbered below $k$ and leaving the others free; each is prime by `DiazModulus.isPrime_iInf_ker_eval_of_analytic`, and $Y_iZ_i - 1$ separates consecutive members.
--
--   **Novelty.** Classical; routine formalisation.
-- source:
--   Classical dimension theory: the torus $\mathbb{G}_m^{A_1}$ has codimension $|A_1|$ in $\mathbb{A}^{2|A_1|}$. Uses `DiazModulus.isPrime_iInf_ker_eval_of_analytic`. C1.3 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Definitions.Def_DiazHilbertBox

namespace DiazModulus

theorem le_height_torusVanishing {A₀ A₁ : Type*} [Fintype A₀] [Fintype A₁] :
    (Fintype.card A₁ : ℕ∞) ≤
      (⨅ (x : A₀ → ℂ) (y : A₁ → ℂˣ),
        RingHom.ker (MvPolynomial.eval (torusPoint x y) :
          MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ →+* ℂ)).height := by
  sorry

end DiazModulus
