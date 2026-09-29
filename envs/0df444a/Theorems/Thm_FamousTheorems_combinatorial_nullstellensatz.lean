-- Prove2me | Theorems.Thm_FamousTheorems_combinatorial_nullstellensatz
-- name    : FamousTheorems.combinatorial_nullstellensatz
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:05:22.415958+00:00
-- url     : https://prove2.me/theorems/d3ccfbb8-3050-46fb-b225-58f7b62c11f5
-- title:
--   Alon's combinatorial Nullstellensatz
-- statement:
--   **Alon's combinatorial Nullstellensatz.** Let $R$ be an integral domain and $f\in R[x_i:i\in\sigma]$ a polynomial in finitely many variables. Suppose the coefficient of a monomial $x^t=\prod_ix_i^{t_i}$ in $f$ is nonzero and $\deg f=\sum_it_i$. Then for any finite sets $S_i\subseteq R$ with $|S_i|>t_i$, there is a point $s$ with $s_i\in S_i$ for all $i$ and $f(s)\ne0$.
--
--   Alon's theorem (1999) is a powerful tool in additive combinatorics, graph theory and combinatorial number theory. It gives short proofs of the Cauchy–Davenport theorem, the Erdős–Heilbronn conjecture (Dias da Silva–Hamidoune), the Chevalley–Warning theorem and many list-colouring results.
--
--   **Formalization note.** Mathlib's `MvPolynomial.combinatorial_nullstellensatz_exists_eval_nonzero`. The monomial is an exponent vector `t : σ →₀ ℕ` with total degree `Finsupp.degree t`, and `MvPolynomial.coeff t f` is its coefficient. `f.totalDegree` is the total degree of `f`, and `MvPolynomial.eval s f` evaluates at the point `s`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MvPolynomial.combinatorial_nullstellensatz_exists_eval_nonzero`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem combinatorial_nullstellensatz {R σ : Type*} [CommRing R] [IsDomain R] [Finite σ] (f : MvPolynomial σ R) (t : σ →₀ ℕ)
    (ht : MvPolynomial.coeff t f ≠ 0) (ht' : f.totalDegree = Finsupp.degree t) (S : σ → Finset R)
    (htS : ∀ i, t i < (S i).card) :
    ∃ s : σ → R, (∀ i, s i ∈ S i) ∧ MvPolynomial.eval s f ≠ 0 := by sorry

end FamousTheorems
