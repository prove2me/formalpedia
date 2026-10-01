-- Prove2me | Theorems.Thm_ChenWhitt93_Reflection_colNorm_geometric_series_bound
-- name    : ChenWhitt93.Reflection.colNorm_geometric_series_bound
-- status  : Open
-- author  : @junyihjy
-- created : 2026-10-01T07:36:53.765394+00:00
-- url     : https://prove2.me/theorems/2c2c9671-679d-487d-873b-22edcdbc65e6
-- title:
--   Neumann-series norm bound for the reflection-matrix geometric series
-- statement:
--   For a real n-by-n matrix Q and a nonnegative submultiplicative norm with ||Q||<=1 and ||Q^n||<1, sum_{k>=0} ||Q^k|| converges and is at most n/(1-||Q^n||).
-- source:
--   Chen and Whitt, Diffusion approximations for open queueing networks with service interruptions, Queueing Systems 13 (1993), bound used in Eqs. (2.8) and (2.10), p. 339

import Mathlib

open Filter Topology Matrix

namespace ChenWhitt93.Reflection

/-- Chen and Whitt (1993), the bound behind Eqs. (2.8) and (2.10): for a real
`n x n` matrix `Q` and a nonnegative submultiplicative matrix norm `normM`
with `normM Q <= 1` and `normM (Q ^ n) < 1`, the norm series `Summable fun k =>
normM (Q ^ k)` converges and is at most `n / (1 - normM (Q ^ n))`. -/
theorem colNorm_geometric_series_bound {n : Nat} (Q : Matrix (Fin n) (Fin n) Real)
    (normM : Matrix (Fin n) (Fin n) Real -> Real)
    (hsub : forall A B : Matrix (Fin n) (Fin n) Real, normM (A * B) <= normM A * normM B)
    (hnonneg : forall A : Matrix (Fin n) (Fin n) Real, 0 <= normM A)
    (hn : 1 <= n) (hQ1 : normM Q <= 1) (hgam : normM (Q ^ n) < 1) :
    Summable (fun k : Nat => normM (Q ^ k)) /\
      (tsum fun k : Nat => normM (Q ^ k)) <= (n : Real) / (1 - normM (Q ^ n)) := by sorry

end ChenWhitt93.Reflection
