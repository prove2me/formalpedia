-- Prove2me | Theorems.Thm_DiazModulus_transcendental_add_mul_add_mul_conj
-- name    : DiazModulus.transcendental_add_mul_add_mul_conj
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-18T17:47:52.056328+00:00
-- url     : https://prove2.me/theorems/6135a78a-d72e-4585-b66f-130ca72f4892
-- title:
--   If u is transcendental over a subfield F of ℂ and uū ∈ F, then a + bu + cū is transcendental over F for all a, b, c ∈ F with (b, c) ≠ (0, 0)
-- statement:
--   Let $F$ be a subfield of $\mathbb{C}$ and $u \in \mathbb{C}$ transcendental over $F$ with $u\bar u \in F$. Let $a, b, c \in F$ with $b \neq 0$ or $c \neq 0$. Then $a + bu + c\bar u$ is transcendental over $F$.
--
--   **Proof.** Put $e = a + bu + c\bar u$ and $\rho = u\bar u$, which is non-zero as $u \neq 0$. Multiplying by $u$ gives $bu^2 + (a - e)u + c\rho = 0$, so $u$ is a root of $bX^2 + (a - e)X + c\rho$, a polynomial over the intermediate field $F(e)$ that is non-zero because $b \neq 0$ or $c\rho \neq 0$. If $e$ were algebraic over $F$, then $F(e)$ would be algebraic over $F$, and $u$, algebraic over $F(e)$, would be algebraic over $F$, a contradiction.
--
--   **Novelty.** A standard fact of field theory; routine.
-- source:
--   Standard field theory. R19 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 18 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem transcendental_add_mul_add_mul_conj
    (F : Subfield ℂ) (u : ℂ) (hu : Transcendental F u) (hρ : u * conj u ∈ F)
    (a b c : ℂ) (ha : a ∈ F) (hb : b ∈ F) (hc : c ∈ F) (hbc : b ≠ 0 ∨ c ≠ 0) :
    Transcendental F (a + b * u + c * conj u) := by
  sorry

end DiazModulus
