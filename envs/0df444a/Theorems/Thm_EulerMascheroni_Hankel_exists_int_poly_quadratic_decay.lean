-- Prove2me | Theorems.Thm_EulerMascheroni_Hankel_exists_int_poly_quadratic_decay
-- name    : EulerMascheroni.Hankel.exists_int_poly_quadratic_decay
-- status  : Open
-- author  : @shivm
-- created : 2026-10-04T13:58:06.196236+00:00
-- url     : https://prove2.me/theorems/2611148d-094a-4e0e-b1d3-54582349ccdc
-- title:
--   Integer polynomials of linear degree with $0<Q_n(\gamma)<e^{-cn^2}$
-- statement:
--   There are $D\in\mathbb N$, $c>0$ and, for all large $n$, $Q_n\in\mathbb Z[X]$ with $\deg Q_n\le Dn$ and $0<Q_n(\gamma)<e^{-cn^2}$.
--
--   This is the $\gamma$-analogue of Fauzan's main estimate for $\zeta(5)$ (`Apery.main_estimate`). No height bound is needed: $b^{Dn}e^{-cn^2}\to0$, so it implies $\gamma\notin\mathbb Q$.
-- source:
--   A. Fauzan, ζ(5) is irrational (2026), https://zenodo.org/records/22826419, Thm. 2.1 and §1.1 (the argument there, with ζ(5) replaced by γ).

import Mathlib

open Polynomial Filter Topology

namespace EulerMascheroni.Hankel

theorem exists_int_poly_quadratic_decay :
    ∃ D : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∃ Q : ℤ[X], Q.natDegree ≤ D * n ∧
      0 < aeval Real.eulerMascheroniConstant Q ∧
      aeval Real.eulerMascheroniConstant Q < Real.exp (-c * (n : ℝ) ^ 2) := by sorry

end EulerMascheroni.Hankel
