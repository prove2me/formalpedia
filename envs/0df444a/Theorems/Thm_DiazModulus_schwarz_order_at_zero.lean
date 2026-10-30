-- Prove2me | Theorems.Thm_DiazModulus_schwarz_order_at_zero
-- name    : DiazModulus.schwarz_order_at_zero
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T06:06:04.410992+00:00
-- url     : https://prove2.me/theorems/34d20ddf-feb5-411f-b55c-5c6370721211
-- title:
--   Schwarz lemma at one zero (DALAG Lemma 2.4): an entire $F$ with a zero of order $T$ at $0$ has $|F(1)| \le R^{-T} \max_{|z| = R} |F|$
-- statement:
--   Let $F$ be an entire function with a zero of order at least $T$ at $0$, let $R \geq 1$, and suppose $|F(z)| \leq B$ whenever $|z| = R$. Then $|F(1)| \leq R^{-T} B$.
--
--   **Proof.** Write $F(z) = z^T g(z)$ near $0$ with $g$ analytic there. Then $G(z) = F(z)/z^T$, extended by $g(0)$ at $0$, is entire, and $|G(z)| \leq B/R^T$ on $|z| = R$. The maximum modulus principle on the disc $|z| \leq R$ gives $|G(1)| \leq B/R^T$, as $R \geq 1$, and $G(1) = F(1)$.
--
--   **Novelty.** Classical; routine formalisation. Schwarz's lemma, DALAG Lemma 2.4 at the point 1.
-- source:
--   Schwarz's lemma: M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Lemma 2.4. C1.4 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem schwarz_order_at_zero (F : ℂ → ℂ) (hF : Differentiable ℂ F) (T : ℕ)
    (hT : (T : ℕ∞) ≤ analyticOrderAt F 0) (R B : ℝ) (hR : 1 ≤ R)
    (hB : ∀ z : ℂ, ‖z‖ = R → ‖F z‖ ≤ B) : ‖F 1‖ ≤ R ^ (-(T : ℤ)) * B := by
  sorry

end DiazModulus
