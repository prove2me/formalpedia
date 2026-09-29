-- Prove2me | Theorems.Thm_FamousTheorems_galois_group_symmetric_prime_degree_6b
-- name    : FamousTheorems.galois_group_symmetric_prime_degree_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:43:35.447905+00:00
-- url     : https://prove2.me/theorems/532ebc8f-6696-4b0e-a238-76b545e38385
-- title:
--   Irreducible rational polynomials of prime degree with exactly two non-real roots have Galois group Sₚ
-- statement:
--   **Irreducible rational polynomials of prime degree with exactly two non-real roots have Galois group $S_p$.** Let $f\in\mathbb Q[x]$ be irreducible of prime degree $p$ with exactly two non-real complex roots. Then the action of the Galois group of $f$ on the $p$ complex roots of $f$ gives an isomorphism
--   $$\operatorname{Gal}(f)\cong S_p.$$
--
--   The Galois group contains a $p$-cycle, since $p$ divides its order, and a transposition, namely complex conjugation. These two elements generate $S_p$. The theorem gives explicit quintics, such as $x^5-4x+2$, whose Galois group is $S_5$ and which are therefore not solvable by radicals.
--
--   **Formalization note.** Mathlib's `Polynomial.Gal.galActionHom_bijective_of_prime_degree`. `Polynomial.Gal.galActionHom p ℂ` is the permutation action of `p.Gal` on `p.rootSet ℂ`. It needs an instance saying that $f$ splits over $\mathbb C$, supplied here explicitly as `Polynomial.Gal.splits_ℚ_ℂ`. The hypothesis on the roots says that $f$ has exactly two more complex roots than real roots.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Polynomial.Gal.galActionHom_bijective_of_prime_degree`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem galois_group_symmetric_prime_degree_6b {p : Polynomial ℚ} (hirr : Irreducible p) (hdeg : p.natDegree.Prime)
    (hroots : Fintype.card (p.rootSet ℂ) = Fintype.card (p.rootSet ℝ) + 2) :
    Function.Bijective (@Polynomial.Gal.galActionHom ℚ _ p ℂ _ _ Polynomial.Gal.splits_ℚ_ℂ) := by sorry

end FamousTheorems
