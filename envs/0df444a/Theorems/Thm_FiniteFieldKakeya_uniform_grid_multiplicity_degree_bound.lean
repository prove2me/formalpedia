-- Prove2me | Theorems.Thm_FiniteFieldKakeya_uniform_grid_multiplicity_degree_bound
-- name    : FiniteFieldKakeya.uniform_grid_multiplicity_degree_bound
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T06:21:38.690748+00:00
-- url     : https://prove2.me/theorems/ba9f2f98-6b25-451f-9609-a18ce869aa00
-- title:
--   Uniform multiplicity bound on a finite field grid
-- statement:
--   Let $F$ be a finite field with $q=|F|$, and let $d,r$ be nonnegative integers. Let $P$ be a nonzero polynomial in $d$ variables over $F$. Suppose that for every point $a\in F^d$, every coefficient of total degree less than $r$ in $P(X+a)$ vanishes. Equivalently, $P$ has Hasse multiplicity at least $r$ at every point of the field grid. Then
--
--   $$\deg P\ge rq.$$
--
--   This includes $d=0$ and $r=0$. It is the uniform-multiplicity finite-field grid bound, used to detect vanishing of polynomials in the sharp finite-field Kakeya proof. No characteristic-zero assumption or factorial division is used.
-- source:
--   Bukh and Chao, Sharp density bounds on the finite field Kakeya problem, arXiv:2108.00074v2, Discrete Analysis 2021:26, p. 4, Lemma 7 (uniform multiplicity version of generalized Schwartz–Zippel). Necessary reusable input for Lemma 9 and public target FCP.Kakeya.kakeya_finite_field (448b0e69-57fd-4028-ab8b-07964b7b3c5b). A direct formal proof by dimension/order induction is supplied separately.

import Mathlib

theorem FiniteFieldKakeya.uniform_grid_multiplicity_degree_bound {F : Type*} [Field F] [Fintype F]
    (d r : ℕ) (P : MvPolynomial (Fin d) F) (hP : P ≠ 0)
    (hjet : ∀ a : Fin d → F, ∀ i : Fin d →₀ ℕ,
      i.sum (fun _ e => e) < r →
        MvPolynomial.coeff i (MvPolynomial.eval₂ MvPolynomial.C
          (fun j => MvPolynomial.X j + MvPolynomial.C (a j)) P) = 0) :
    r * Fintype.card F ≤ P.totalDegree := by sorry
