-- Prove2me | Theorems.Thm_ChatterjeeQFT_single_particle_spaces_poincare_invariant
-- name    : ChatterjeeQFT.single_particle_spaces_poincare_invariant
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T21:43:19.028026+00:00
-- url     : https://prove2.me/theorems/bd7ca1ae-8ce3-409a-9376-db733d0d201f
-- title:
--   The one-particle boson and electron spaces carry unitary Poincaré actions
-- statement:
--   **Goal of the mission.** The two one-particle state spaces built in these lectures — the
--   massive scalar boson space $L^2(X_m, d\lambda_m)$ and the electron space
--   $L^2(X_m, d\lambda_m, \mathbb{C}^2)$ with the weighted inner product — both carry inner products
--   that are invariant under the Poincaré action, so that the representations of Lecture 11 §11.3 and
--   Lecture 25 §25.3 are unitary.
--
--   Precisely: let $m > 0$, let $a \in \mathbb{R}^{1,3}$ be a spacetime translation, let
--   $A \in SL(2,\mathbb{C})$, and let $L$ be the Lorentz transformation induced by $A$, i.e.
--   $\kappa(A)x = Lx$ for all $x$. Then
--
--   1. **(boson)** for all $\psi, \varphi \in L^2(X_m, d\lambda_m)$,
--   $$\int_{X_m} \overline{(U(a,L)\psi)}\,(U(a,L)\varphi)\, d\lambda_m
--   = \int_{X_m} \overline{\psi}\,\varphi\, d\lambda_m,
--   \qquad (U(a,L)\psi)(p) = e^{i(a,p)}\psi(L^{-1}p);$$
--
--   2. **(electron)** for all $\psi, \varphi$ in the weighted space,
--   $$\int_{X_m} (U(a,A)\psi)^{\dagger} V_p^{-2} (U(a,A)\varphi)\, d\lambda_m
--   = \int_{X_m} \psi^{\dagger} V_p^{-2}\varphi\, d\lambda_m,
--   \qquad (U(a,A)\psi)(p) = e^{i(a,p)} A\,\psi(\kappa(A)^{-1}p).$$
--
--   The two clauses are tied together by the single group element: the Lorentz transformation acting
--   on the scalar wave function is the image under $\kappa$ of the $SL(2,\mathbb{C})$ element acting on
--   the spinor wave function. Part 1 rests on the Lorentz invariance of $\lambda_m$; part 2 needs in
--   addition Lemma 25.1, which is exactly what the weight $V_p^{-2}$ was designed to provide.
-- source:
--   S. Chatterjee, *Lectures on Quantum Field Theory* (Stanford, 2018-19, combined scribed lecture notes), https://souravchatterjee.su.domains/qft-lectures-combined.pdf, Lecture 11 §11.3 p. 45 (scalar bosons) and Lecture 25 §25.3 pp. 108-109 (electrons; the inner product and Lemma 25.1 are introduced precisely to make the representation unitary).

import Mathlib
import Definitions.Def_ChatterjeeQFT_ElectronSpace
open MeasureTheory Matrix
open scoped ENNReal ComplexOrder

namespace ChatterjeeQFT

theorem single_particle_spaces_poincare_invariant (m : ℝ) (hm : 0 < m) (a : Fin 4 → ℝ)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : ∀ x : Fin 4 → ℝ, kappa A x = L *ᵥ x) :
    (∀ ψ φ : (Fin 4 → ℝ) → ℂ, MemLp ψ 2 (massShellMeasure m) → MemLp φ 2 (massShellMeasure m) →
        ∫ p, (starRingEnd ℂ) (bosonAction a L ψ p) * bosonAction a L φ p ∂(massShellMeasure m)
          = ∫ p, (starRingEnd ℂ) (ψ p) * φ p ∂(massShellMeasure m)) ∧
      (∀ ψ φ : (Fin 4 → ℝ) → (Fin 2 → ℂ), ψ ∈ ElectronL2 m → φ ∈ ElectronL2 m →
        electronInner m (electronAction a A ψ) (electronAction a A φ) = electronInner m ψ φ) := by
  sorry

end ChatterjeeQFT
