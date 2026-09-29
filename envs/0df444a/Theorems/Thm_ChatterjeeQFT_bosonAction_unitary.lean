-- Prove2me | Theorems.Thm_ChatterjeeQFT_bosonAction_unitary
-- name    : ChatterjeeQFT.bosonAction_unitary
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T21:35:39.498707+00:00
-- url     : https://prove2.me/theorems/25ee4f69-c956-42da-87d5-96e7b2348c96
-- title:
--   Unitarity of the scalar representation on $L^2(X_m, d\lambda_m)$
-- statement:
--   The scalar representation of the Poincaré group preserves the inner product of
--   $L^2(X_m, d\lambda_m)$: for $m>0$, $a \in \mathbb{R}^{1,3}$, $L \in SO^{\uparrow}(1,3)$ and
--   $\psi, \varphi \in L^2(X_m, d\lambda_m)$,
--
--   $$\int_{X_m} \overline{(U(a,L)\psi)(p)}\,(U(a,L)\varphi)(p)\, d\lambda_m(p)
--   \;=\; \int_{X_m} \overline{\psi(p)}\,\varphi(p)\, d\lambda_m(p).$$
--
--   The phase $e^{i(a,p)}$ cancels between the two factors, and the change of variables $p \mapsto Lp$
--   is absorbed by the Lorentz invariance of $\lambda_m$. Together with the composition law this says
--   that $U$ is a unitary representation on the one-particle boson space.
-- source:
--   S. Chatterjee, *Lectures on Quantum Field Theory* (Stanford, 2018-19, combined scribed lecture notes), https://souravchatterjee.su.domains/qft-lectures-combined.pdf, Lecture 11 §11.3, p. 45 (the representation for massive scalar bosons is unitary on $H = L^2(X_m, d\lambda_m)$).

import Mathlib
import Definitions.Def_ChatterjeeQFT_MassShell
open MeasureTheory Matrix
open scoped ENNReal

namespace ChatterjeeQFT

theorem bosonAction_unitary (m : ℝ) (hm : 0 < m) (a : Fin 4 → ℝ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsRestrictedLorentz L)
    (ψ φ : (Fin 4 → ℝ) → ℂ) (hψ : MemLp ψ 2 (massShellMeasure m))
    (hφ : MemLp φ 2 (massShellMeasure m)) :
    ∫ p, (starRingEnd ℂ) (bosonAction a L ψ p) * bosonAction a L φ p ∂(massShellMeasure m)
      = ∫ p, (starRingEnd ℂ) (ψ p) * φ p ∂(massShellMeasure m) := by sorry

end ChatterjeeQFT
