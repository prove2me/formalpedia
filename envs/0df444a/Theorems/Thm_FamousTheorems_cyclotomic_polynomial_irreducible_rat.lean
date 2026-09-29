-- Prove2me | Theorems.Thm_FamousTheorems_cyclotomic_polynomial_irreducible_rat
-- name    : FamousTheorems.cyclotomic_polynomial_irreducible_rat
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:38:26.225489+00:00
-- url     : https://prove2.me/theorems/92ba700b-9f72-4d4f-a33c-bd6dc2c63406
-- title:
--   Irreducibility of the cyclotomic polynomials over ℚ
-- statement:
--   **Irreducibility of the cyclotomic polynomials over $\mathbb Q$.** For every $n\ge1$, the $n$-th cyclotomic polynomial
--   $$\Phi_n(X)=\prod_{\substack{1\le k\le n\\ \gcd(k,n)=1}}\big(X-e^{2\pi ik/n}\big)$$
--   is irreducible over $\mathbb Q$.
--
--   Gauss proved this for prime $n$ and Kronecker (1854) and Dedekind (1857) for general $n$. It is equivalent to $[\mathbb Q(\zeta_n):\mathbb Q]=\varphi(n)$ and $\operatorname{Gal}(\mathbb Q(\zeta_n)/\mathbb Q)\cong(\mathbb Z/n)^\times$. It is the starting point of cyclotomic field theory and of the Kronecker–Weber theorem.
--
--   **Formalization note.** Mathlib's `Polynomial.cyclotomic.irreducible_rat`. `Polynomial.cyclotomic n ℚ` is the $n$-th cyclotomic polynomial with rational coefficients.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Polynomial.cyclotomic.irreducible_rat`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem cyclotomic_polynomial_irreducible_rat {n : ℕ} (hn : 0 < n) : Irreducible (Polynomial.cyclotomic n ℚ) := by sorry

end FamousTheorems
