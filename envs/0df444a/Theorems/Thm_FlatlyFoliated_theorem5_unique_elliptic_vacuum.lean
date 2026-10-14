-- Prove2me | Theorems.Thm_FlatlyFoliated_theorem5_unique_elliptic_vacuum
-- name    : FlatlyFoliated.theorem5_unique_elliptic_vacuum
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T20:43:09.851059+00:00
-- url     : https://prove2.me/theorems/f12edcc5-43f4-460b-919f-b48ece844ef1
-- title:
--   Theorem 5 — unique vacuum solution of the elliptic FFR equations ($\Lambda>0$)
-- statement:
--   Let $\Lambda>0$.
--
--   1. (Existence) $f_0(x)=\sqrt{\Lambda/12}\,|x|^2$, $\zeta=0$, $\eta=1$ is a smooth vacuum solution of the elliptic form (39)–(41) (with $\mu=0$, $J=0$), with $\Delta f_0>0$, $f_0$ approximately spherically symmetric at infinity, and satisfying the boundary conditions $\zeta\to0$, $\eta\to1$.
--   2. (Uniqueness) If smooth $(f,\zeta,\eta)$ with $\eta>0$ and $\Delta f/\eta>0$ solve the vacuum elliptic system, $f$ is approximately spherically symmetric at infinity, and
--   $$\lim_{x\to\infty}\zeta(x)=0\ \ (67),\qquad \lim_{x\to\infty}\eta(x)=1\ \ (68),$$
--   then $\zeta\equiv0$, $\eta\equiv1$ and $f(x)=\sqrt{\Lambda/12}\,|x|^2+c$ for some constant $c$.
--
--   So the solution is unique up to an additive constant in $f$.
--
--   **Formalization Note** The arrow-of-time convention $\Delta f/\eta>0$, used in the paper's proof, is an explicit hypothesis; without it $-f_0$ would be a second solution.
-- source:
--   Bray, Hamm, Hirsch, Wheeler, Zhang, Flatly Foliated Relativity, arXiv:1911.00967v2, https://arxiv.org/abs/1911.00967, p. 16, Theorem 5 (with boundary conditions (67), (68), Convention 1 eq. (54); explicit solution eq. (100))

import Mathlib
import Definitions.Def_FlatlyFoliatedRelativity_basic

open scoped ContDiff

namespace FlatlyFoliated

/-- Theorem 5: for `Λ > 0`, under (67), (68) and approximate spherical symmetry at `∞`,
the elliptic vacuum system has exactly the solutions `f = √(Λ/12) r² + c`, `ζ = 0`, `η = 1`. -/
theorem theorem5_unique_elliptic_vacuum (Λ : ℝ) (hΛ : 0 < Λ) :
    (ContDiff ℝ ∞ (fun x : R3 => Real.sqrt (Λ / 12) * ‖x‖ ^ 2) ∧
      (∀ x, 0 < lap (fun x : R3 => Real.sqrt (Λ / 12) * ‖x‖ ^ 2) x) ∧
      EllipticSystem Λ 0 0 (fun x : R3 => Real.sqrt (Λ / 12) * ‖x‖ ^ 2) 0 (fun _ => 1) ∧
      ApproxSphSymmAtInfty (fun x : R3 => Real.sqrt (Λ / 12) * ‖x‖ ^ 2) ∧
      Filter.Tendsto (0 : R3 → R3) (Bornology.cobounded R3) (nhds 0) ∧
      Filter.Tendsto (fun _ : R3 => (1 : ℝ)) (Bornology.cobounded R3) (nhds 1)) ∧
    ∀ (f : R3 → ℝ) (ζ : R3 → R3) (η : R3 → ℝ),
      ContDiff ℝ ∞ f → ContDiff ℝ ∞ ζ → ContDiff ℝ ∞ η → (∀ x, 0 < η x) →
      (∀ x, 0 < lap f x / η x) →
      EllipticSystem Λ 0 0 f ζ η → ApproxSphSymmAtInfty f →
      Filter.Tendsto ζ (Bornology.cobounded R3) (nhds 0) →
      Filter.Tendsto η (Bornology.cobounded R3) (nhds 1) →
      ∃ c : ℝ, (∀ x, f x = Real.sqrt (Λ / 12) * ‖x‖ ^ 2 + c) ∧ ζ = 0 ∧ η = fun _ => 1 := by sorry

end FlatlyFoliated
