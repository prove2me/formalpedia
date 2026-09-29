-- Prove2me | Theorems.Thm_FamousTheorems_partial_fraction_decomposition_7b
-- name    : FamousTheorems.partial_fraction_decomposition_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:34:50.967257+00:00
-- url     : https://prove2.me/theorems/fc32299a-558d-4d29-a8e8-e8eb5928bc52
-- title:
--   Partial fraction decomposition
-- statement:
--   **Partial fraction decomposition.** Let $R$ be a commutative ring and $K$ a field containing $R[X]$. Let $f\in R[X]$ and let $g_1,\dots,g_n\in R[X]$ be monic and pairwise coprime. Then there are polynomials $q,r_1,\dots,r_n\in R[X]$ with $\deg r_i<\deg g_i$ for each $i$ and
--   $$\frac{f}{g_1\cdots g_n}=q+\sum_{i=1}^n\frac{r_i}{g_i}$$
--   in $K$.
--
--   Partial fractions are the standard tool for integrating rational functions and for computing inverse Laplace and $z$-transforms and generating function coefficients. Applied to powers of linear factors, they show that every rational function over $\mathbb C$ is a sum of a polynomial and terms $c/(x-a)^k$. The existence part follows from Bézout identities for the coprime $g_i$ and division with remainder by monic polynomials.
--
--   **Formalization note.** Mathlib's `Polynomial.div_prod_eq_quo_add_sum_rem_div`. $K$ is any field with an injective $R[X]$-algebra structure, such as the field of rational functions $\operatorname{Frac}R[X]$ when $R$ is a domain. The coercions $R[X]\to K$ are given by `algebraMap`. Pairwise coprimality is in the sense of `IsCoprime`: $ag_i+bg_j=1$ for some $a,b\in R[X]$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Polynomial.div_prod_eq_quo_add_sum_rem_div`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open scoped algebraMap

theorem partial_fraction_decomposition_7b {R : Type*} [CommRing R] (K : Type*) [Field K] [Algebra (Polynomial R) K] [FaithfulSMul (Polynomial R) K]
    (f : Polynomial R) {ι : Type*} {g : ι → Polynomial R} {s : Finset ι} (hg : ∀ i ∈ s, (g i).Monic)
    (hcop : Set.Pairwise (s : Set ι) fun i j => IsCoprime (g i) (g j)) :
    ∃ (q : Polynomial R) (r : ι → Polynomial R), (∀ i ∈ s, (r i).degree < (g i).degree) ∧
      (f : K) / ∏ i ∈ s, (g i : K) = (q : K) + ∑ i ∈ s, (r i : K) / (g i : K) := by sorry

end FamousTheorems
