-- Prove2me | Theorems.Thm_DiazModulus_roy_phi_closed_form_superadd
-- name    : DiazModulus.roy_phi_closed_form_superadd
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T14:07:00.740603+00:00
-- url     : https://prove2.me/theorems/01ba7f8b-0518-4487-9561-0f586d292d9a
-- title:
--   Roy's closed form F(n, d) = nd/(d − n) if n = 1 or d − n = 1, else (d − n)/(d − n − 1) + (n − 1)n: for 0 < a < x and 0 < b < y, ax/(x − a) ≤ F(a, x) and F(a, x) + F(b, y) ≤ F(a + b, x + y)
-- statement:
--   For natural numbers $0 < n < d$ let $F(n, d) = nd/(d - n)$ if $n = 1$ or $d - n = 1$, and $F(n, d) = (d - n)/(d - n - 1) + (n - 1)\,n$ otherwise, a rational number (in the second case $d - n \ge 2$). Then:
--
--   (i) for all natural numbers $0 < a < x$,
--   $$\frac{ax}{x - a} \le F(a, x);$$
--   (ii) for all natural numbers $0 < a < x$ and $0 < b < y$,
--   $$F(a, x) + F(b, y) \le F(a + b, x + y).$$
--   $F(n, d)$ is the value that Roy's Lemma (Roy 1992, p. 40) gives for his maximum $\varphi(n, d)$.
-- source:
--   Step of the proof of D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47, Lemma (p. 40), by superadditivity of the closed form in place of Roy's exchange argument (pp. 40–41); inequality (i) with a ≥ 2 and δ = x − a ≥ 2 is, after subtracting a from both sides, the relation a²/δ ≤ (a − 1)² + 1/(δ − 1) of Roy's proof. Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem roy_phi_closed_form_superadd :
    let F : ℕ → ℕ → ℚ := fun n d =>
      if n = 1 ∨ d - n = 1 then ((n : ℚ) * d) / ((d : ℚ) - n)
      else ((d : ℚ) - n) / ((d : ℚ) - n - 1) + ((n : ℚ) - 1) * n
    (∀ a x : ℕ, 0 < a → a < x → ((a : ℚ) * x) / ((x : ℚ) - a) ≤ F a x) ∧
    ∀ a x b y : ℕ, 0 < a → a < x → 0 < b → b < y → F a x + F b y ≤ F (a + b) (x + y) := by
  sorry

end DiazModulus
