-- Prove2me | Theorems.Thm_DouglasVacua_superpotential_coefficient_count
-- name    : DouglasVacua.superpotential_coefficient_count
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T19:19:41.745826+00:00
-- url     : https://prove2.me/theorems/250539ce-3d1c-4f18-a6cd-4073bb287d85
-- title:
--   Number of coefficients of a degree-$d$ polynomial in $n$ variables: $(d+n)!/(d!\,n!)$
-- statement:
--   For all $n,d\in\mathbb N$:
--   $$\#\{I\in\mathbb N^n : I_1+\dots+I_n\le d\}=\frac{(d+n)!}{d!\,n!}=\#\{I\in\mathbb N^{n+1}: I_1+\dots+I_{n+1}=d\}.$$
--   That is, a polynomial of degree $d$ in $n$ variables has $c(d,n)=(d+n)!/(d!n!)$ coefficients, the number of degree-$d$ homogeneous monomials in $n+1$ variables. For $d=3$ this gives the $(n+1)(n+2)(n+3)/6$ coefficients of the cubic superpotential (4.5).
-- source:
--   Michael R. Douglas, *The statistics of string/M theory vacua*, JHEP 05 (2003) 046, https://doi.org/10.1088/1126-6708/2003/05/046 (arXiv:hep-th/0303194). Section 4, p. 35 ("Such a polynomial has $c(d,n)=(d+n)!/d!n!$ independent coefficients (the number of degree $d$ homogeneous polynomials in $n+1$ variables)"); also p. 37, below eq. (4.5).

import Mathlib
open Nat

namespace DouglasVacua

theorem superpotential_coefficient_count (n d : ℕ) :
    (Set.ncard {e : Fin n → ℕ | ∑ i, e i ≤ d} : ℚ) = (d + n)! / (d ! * n !) ∧
    (Set.ncard {e : Fin (n + 1) → ℕ | ∑ i, e i = d} : ℚ) = (d + n)! / (d ! * n !) := by sorry

end DouglasVacua
