-- Prove2me | Theorems.Thm_FamousTheorems_mul_esymm_eq_sum
-- name    : FamousTheorems.mul_esymm_eq_sum
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T08:37:35.228508+00:00
-- url     : https://prove2.me/theorems/ba3de7e7-6384-40b8-bcba-38e9f2435cd7
-- title:
--   Newton's identities
-- statement:
--   **Newton's identities** relating elementary symmetric polynomials to power sums. For each $k$, $$k\,e_k = (-1)^{k+1}\sum_{i+j=k,\ i<k} (-1)^i e_i\, p_j,$$ where $e_k$ is the $k$-th elementary symmetric polynomial and $p_j$ the $j$-th power sum. The identities let one convert between the two standard bases of the symmetric functions recursively: knowing $p_1,\dots,p_k$ determines $e_1,\dots,e_k$ and conversely. Since the $e_k$ are the coefficients of a polynomial and the $p_j$ are sums of powers of its roots, this is the systematic way to compute power sums of roots without finding the roots — the basis of Newton's method for bounding roots and of the Faddeev–LeVerrier algorithm for characteristic polynomials. The factor $k$ on the left means the conversion requires dividing by integers, so the identities behave differently in positive characteristic. Newton stated them around 1666; Girard had special cases earlier. **Formalization note.** `MvPolynomial.esymm` and `psum` are the elementary symmetric polynomials and power sums; the sum is over the antidiagonal of $k$ restricted to $i < k$. The result is Mathlib's `MvPolynomial.mul_esymm_eq_sum`.
-- source:
--   Listed in Mathlib's undergraduate/overview curriculum manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem mul_esymm_eq_sum :
    ∀ (σ : Type u_1) [inst : Fintype σ] (R : Type u_2) [inst_1 : CommRing R] (k : ℕ), 
    ↑k * MvPolynomial.esymm σ R k = 
    (-1) ^ (k + 1) * 
    ∑ a ∈ Finset.HasAntidiagonal.antidiagonal k with a.1 < k, 
    (-1) ^ a.1 * MvPolynomial.esymm σ R a.1 * MvPolynomial.psum σ R a.2 := by sorry

end FamousTheorems
