-- Prove2me | Theorems.Thm_FlatlyFoliated_corollary2_unique_vacuum
-- name    : FlatlyFoliated.corollary2_unique_vacuum
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T20:44:46.464616+00:00
-- url     : https://prove2.me/theorems/b09c40d1-632e-4462-a198-82155db45379
-- title:
--   Corollary 2 — $\Lambda>0$ implies a unique vacuum solution of FFR
-- statement:
--   Let $\Lambda>0$.
--
--   1. (Existence) $\omega_0(x)=\sqrt{\Lambda/3}\,x$ (i.e. $\omega_0=\sqrt{\Lambda/3}\,r\,dr$) and $\eta_0=1$ form a smooth vacuum solution of the FFR equations (34)–(35) (with $\mu=0$, $J=0$) that satisfies $(\nabla\cdot\omega_0)/\eta_0>0$ and is spherically symmetric at infinity.
--   2. (Uniqueness) If smooth $(\omega,\eta)$ with $\eta>0$ and $(\nabla\cdot\omega)/\eta>0$ solve the vacuum FFR equations and are spherically symmetric at infinity, then for some constant $c>0$
--   $$\eta\equiv c,\qquad \omega(x)=c\sqrt{\Lambda/3}\;x .$$
--
--   So the vacuum solution is unique up to an overall positive constant, i.e. a rescaling of the time coordinate.
--
--   **Formalization Note** The arrow-of-time convention $(\nabla\cdot\omega)/\eta>0$ (Convention 1, in force for $\Lambda>0$) is an explicit hypothesis; without it the time-reversed solution $-\omega_0$ also exists.
-- source:
--   Bray, Hamm, Hirsch, Wheeler, Zhang, Flatly Foliated Relativity, arXiv:1911.00967v2, https://arxiv.org/abs/1911.00967, p. 19, Corollary 2 (Section 5; uniqueness up to positive constant and smoothness with η > 0 as defined on p. 15; Convention 1, eq. (54); explicit solution p. 20, ω = √(Λ/3) r dr)

import Mathlib
import Definitions.Def_FlatlyFoliatedRelativity_basic

open scoped ContDiff

namespace FlatlyFoliated

/-- **Goal — Corollary 2**: for `Λ > 0` there is a unique (up to an overall positive
constant, i.e. rescaling of `t`) smooth vacuum solution of (34)–(35) with `η > 0` that is
spherically symmetric at infinity (with the arrow-of-time convention `(∇·w)/η > 0`), namely
`w = √(Λ/3) r ∂ᵣ`, `η = 1`. -/
theorem corollary2_unique_vacuum (Λ : ℝ) (hΛ : 0 < Λ) :
    (ContDiff ℝ ∞ (fun x : R3 => Real.sqrt (Λ / 3) • x) ∧
      (∀ x, 0 < divg (fun x : R3 => Real.sqrt (Λ / 3) • x) x / 1) ∧
      FFREquations Λ 0 0 (fun x : R3 => Real.sqrt (Λ / 3) • x) (fun _ => 1) ∧
      SphSymmAtInfty (fun x : R3 => Real.sqrt (Λ / 3) • x) (fun _ => 1)) ∧
    ∀ (w : R3 → R3) (η : R3 → ℝ),
      ContDiff ℝ ∞ w → ContDiff ℝ ∞ η → (∀ x, 0 < η x) → (∀ x, 0 < divg w x / η x) →
      FFREquations Λ 0 0 w η → SphSymmAtInfty w η →
      ∃ c : ℝ, 0 < c ∧ η = (fun _ => c) ∧ w = fun x => (c * Real.sqrt (Λ / 3)) • x := by sorry

end FlatlyFoliated
