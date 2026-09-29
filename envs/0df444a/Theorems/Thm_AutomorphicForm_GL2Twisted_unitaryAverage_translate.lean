-- Prove2me | Theorems.Thm_AutomorphicForm_GL2Twisted_unitaryAverage_translate
-- name    : AutomorphicForm.GL2Twisted.unitaryAverage_translate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/bd9b9144-4e1a-5a35-8855-23424ff2d1e3
-- title:
--   Bi-invariance of the unitary chart average on GL₂(ℂ)
-- statement:
--   Let $F : \mathrm{GL}_2(\mathbb{C}) \to \mathbb{C}$ be continuous, and let $k_0, k_1 \in \mathrm{GL}_2(\mathbb{C})$ satisfy $k_0^{*}k_0 = 1$ and $k_1^{*}k_1 = 1$, where $k^{*}$ denotes the conjugate transpose of the underlying $2\times 2$ complex matrix. Then `unitaryAverage` of the translated function $k \mapsto F(k_0 k k_1)$ equals `unitaryAverage` of $F$. Here `unitaryAverage` $F$ is the explicit iterated integral
--   $$\frac{1}{4\pi^3}\int_0^{2\pi}\!\!\int_0^{\pi/2}\!\!\int_0^{2\pi}\!\!\int_0^{2\pi} \sin\eta\,\cos\eta\; F\bigl(\mathrm{unitaryElt}(\psi,\eta,\xi_1,\xi_2)\bigr)\,d\xi_2\,d\xi_1\,d\eta\,d\psi,$$
--   where the integrals are taken in the order $\xi_2$, then $\xi_1$, then $\eta$, then $\psi$, and `unitaryElt` $(\psi,\eta,\xi_1,\xi_2)$ is the invertible matrix
--   $$e^{i\psi}\begin{pmatrix}\cos\eta\, e^{i\xi_1} & \sin\eta\, e^{i\xi_2} \\ -\sin\eta\, e^{-i\xi_2} & \cos\eta\, e^{-i\xi_1}\end{pmatrix},$$
--   whose determinant is $e^{2i\psi} \neq 0$. Taking $k_1 = 1$ gives invariance under left translation by a unitary element, and $k_0 = 1$ invariance under right translation.
--
--   This is the bi-invariance of the normalised Haar average over $U(2)$, realised concretely through the four-parameter Euler-angle chart $(\psi,\eta,\xi_1,\xi_2)$ with density $(4\pi^3)^{-1}\sin\eta\cos\eta$. It is used in the analysis of twisted orbital integrals on $\mathrm{GL}_2(\mathbb{C})$, in particular in the construction of test functions with prescribed vanishing of orbital integrals at regular semisimple elements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_GL2Twisted_unitaryAverage_translate.lean

import Definitions.Def_AutomorphicForm_GL2TwistedOrbitalTransforms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AutomorphicForm.GL2Twisted

theorem AutomorphicForm.GL2Twisted.unitaryAverage_translate (F : GL (Fin 2) ℂ → ℂ) (hF : Continuous F)
    (k₀ k₁ : GL (Fin 2) ℂ)
    (h₀ : star (k₀ : Matrix (Fin 2) (Fin 2) ℂ) * (k₀ : Matrix (Fin 2) (Fin 2) ℂ) = 1)
    (h₁ : star (k₁ : Matrix (Fin 2) (Fin 2) ℂ) * (k₁ : Matrix (Fin 2) (Fin 2) ℂ) = 1) :
    unitaryAverage (fun k => F (k₀ * k * k₁)) = unitaryAverage F := by sorry
