-- Prove2me | Theorems.Thm_DynkinAsymInfo_Linear_lemma_6_5
-- name    : DynkinAsymInfo.Linear.lemma_6_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:18:34.815974+00:00
-- url     : https://prove2.me/theorems/dbb36338-3615-42aa-825f-cbadfe464349
-- title:
--   Lemma 6.5 — type-zero ODE and discounted hitting payoff
-- statement:
--   Let $0<A<B$ and let $\bar V_0$ be $C^1$ on $[A,\infty)$ and $C^2$ on $[A,B]$. Suppose it solves the Euler ODE and all boundary conditions (78)–(79), including $\bar V_0=1$ on $(0,A]$ and $\bar V_0'=0$ from $B$ onwards. For every initial odds $\phi>0$,
--   $$\bar V_0(\phi)=\widetilde E^0_\phi[e^{\mu_0\tau_A}].$$
--   The exponential is zero if the hitting time is infinite. This identifies the type-zero candidate payoff.
--
--   **Formalization Note.** The tilted law $\widetilde P^0$ is realised by the same Brownian path with likelihood drift $\sigma\omega$. The nonnegative expectation is finite under $\mu_0<0$.
-- source:
--   De Angelis, Ekström, Glover, Dynkin Games with Incomplete and Asymmetric Information, arXiv:1810.07674v5, p. 21, Lemma 6.5, (77)–(79)

import Mathlib
import Definitions.Def_DynkinAsymInfo_Linear_ClosedForms

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DynkinAsymInfo.Linear
set_option autoImplicit false

/-- De Angelis, Ekström, Glover, arXiv:1810.07674v5, p. 21, Lemma 6.5
and (78)–(79). A regular solution of the type-zero ODE is the discounted
expectation of the reflected likelihood's hitting time. The source's tilted
measure is realised by a GBM with drift `σω` on the original Brownian space.
On an infinite hitting time the discount is zero. The second equality printed
in the lemma is the definition (77) of V0. -/
theorem lemma_6_5 {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (h62 : p.mu0 < 0 ∧ 0 < p.mu1) (A B : ℝ) (hAB : 0 < A ∧ A < B)
    (v0 : ℝ → ℝ) (hC1 : ContDiffOn ℝ 1 v0 (Set.Ici A))
    (hC2 : ContDiffOn ℝ 2 v0 (Set.Icc A B))
    (hODE : ∀ phi ∈ Set.Ioo A B,
      signalNoise p ^ 2 * phi ^ 2 / 2 * deriv (deriv v0) phi +
      p.sigma * signalNoise p * phi * deriv v0 phi + p.mu0 * v0 phi = 0)
    (hleft : ∀ phi, 0 < phi → phi ≤ A → v0 phi = 1)
    (hB : derivWithin v0 (Set.Icc A B) B = 0)
    (hright : ∀ phi, B ≤ phi → deriv v0 phi = 0)
    (phi : ℝ) (hphi : 0 < phi) :
    discountedHit p st phi A B ≠ ⊤ ∧
      v0 phi = (discountedHit p st phi A B).toReal := by sorry

end DynkinAsymInfo.Linear
