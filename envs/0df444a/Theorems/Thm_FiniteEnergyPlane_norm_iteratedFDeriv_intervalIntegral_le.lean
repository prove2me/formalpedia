-- Prove2me | Theorems.Thm_FiniteEnergyPlane_norm_iteratedFDeriv_intervalIntegral_le
-- name    : FiniteEnergyPlane.norm_iteratedFDeriv_intervalIntegral_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-12T22:32:54.447121+00:00
-- url     : https://prove2.me/theorems/b6b2951b-edc7-4ff9-922b-5d49a441ecf8
-- title:
--   Bounds on derivatives of a parametric integral over $[0,1]$
-- statement:
--   Let $H$ be a finite-dimensional real normed space, $G$ a real Banach space, and $F : H \to \mathbb{R} \to G$ with $(x, t) \mapsto F(x, t)$ of class $C^\infty$. If $\|D^k_x F(x, t)\| \le C$ for all $t \in [0, 1]$, then $\big\|D^k\big(x \mapsto \int_0^1 F(x, t)\,dt\big)(x)\big\| \le C$.
--
--   **Role.** Controls derivatives of Hadamard-type quotients $\int_0^1 Dk(x, \theta w)\,d\theta$.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Lemmas 6.10 and 6.20 (families of fast planes); operators in the setting of C. Wendl, Lectures on Holomorphic Curves in Symplectic and Contact Geometry, arXiv:1011.1690, Ch. 4

import Mathlib

open Metric Set Filter Topology MeasureTheory
open scoped ContDiff

namespace FiniteEnergyPlane

/-- For `F : H → ℝ → G` jointly `C^∞` with `H` finite-dimensional, a bound on the `k`-th
`x`-derivative of `F x t` for `t ∈ [0, 1]` bounds the `k`-th derivative of `x ↦ ∫₀¹ F x t dt`. -/
theorem norm_iteratedFDeriv_intervalIntegral_le {H G : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] [FiniteDimensional ℝ H] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] {F : H → ℝ → G} (hF : ContDiff ℝ ∞ (Function.uncurry F)) (k : ℕ)
    (x : H) (C : ℝ) (hC : ∀ t ∈ Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ k (fun x => F x t) x‖ ≤ C) :
    ‖iteratedFDeriv ℝ k (fun x => ∫ t in (0 : ℝ)..1, F x t) x‖ ≤ C := by
  sorry

end FiniteEnergyPlane
