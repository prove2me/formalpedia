-- Prove2me | Theorems.Thm_Arxiv2608_05214_one_way_decomposition
-- name    : Arxiv2608_05214.one_way_decomposition
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T19:18:39.088162+00:00
-- url     : https://prove2.me/theorems/91c5ccaf-156a-4128-8ca7-bf3afc35e74f
-- title:
--   Eqs. (C-1)-(C-5), (C-7): the two-way system, its eigenvalues $\pm ik_{x_3}$ and the one-way fields
-- statement:
--   Let $\omega\ne0$.
--
--   1. **(C-1).** Let $\rho(x_3)>0$ depend on depth only and let $\kappa(x)>0$ be the bulk modulus. Suppose the frequency-domain pressure $\hat P$ and particle velocity $\hat v$ satisfy eqs. (1)-(2) without sources, $\nabla\hat P=i\omega\rho\,\hat v$ and $-(i\omega/\kappa)\hat P+\nabla\cdot\hat v=0$. Then at every point
--   $$\partial_{x_3}\hat P=i\omega\rho\,\hat V_3,\qquad \partial_{x_3}\hat V_3=\frac{i\omega}{\kappa}\hat P-\frac{\nabla_H^2\hat P}{i\omega\rho},\qquad \nabla_H^2=\partial_{x_1}^2+\partial_{x_2}^2.$$
--   2. **Eigenvalues.** In a homogeneous layer ($\rho,\kappa>0$ constant, $c=\sqrt{\kappa/\rho}$) and in the wavenumber domain ($\nabla_H^2\mapsto-|k_H|^2$), the eigenvalues of the matrix of (C-1) are exactly $\pm i k_{x_3}$, where $k_{x_3}=\sqrt{\omega^2/c^2-|k_H|^2}$ (principal root).
--   3. **(C-7).** $k_{x_3}$ is real and positive for propagating modes, $|k_H|^2<\omega^2/c^2$, and purely imaginary for evanescent modes, $|k_H|^2>\omega^2/c^2$.
--   4. **(C-4)-(C-5) in a homogeneous layer.** If $k_{x_3}\ne0$ and $(\hat P,\hat V_3)$ solves the system of (C-1) in $x_3$, then the pressure-normalised one-way fields $\hat P^\pm=\frac12\hat P\pm\frac{\omega\rho}{2k_{x_3}}\hat V_3$ satisfy
--   $$\partial_{x_3}\hat P^+=ik_{x_3}\hat P^+,\qquad \partial_{x_3}\hat P^-=-ik_{x_3}\hat P^-,$$
--   so the coupling terms vanish.
--
--   **Formalization Note** The density is a function of $x_3$ alone, which (C-1) as printed requires. With $\rho(x_H,x_3)$ the term $\nabla_H^2\hat P/(i\omega\rho)$ would be $\nabla_H\cdot(\rho^{-1}\nabla_H\hat P)/(i\omega)$. The coupling terms of (C-4)-(C-5) in a heterogeneous medium are not given in the paper, so only the homogeneous-layer case is stated.
-- source:
--   H. A. Oyekan, Marchenko Theory, Algorithms, and Applications: A Review, arXiv:2608.05214v1 (2026), claim c023; Appendix C-A (One-Way Decomposition of the Two-Way System), eqs. (C-1)-(C-5), PDF p. 32; Appendix C-B, eq. (C-7), PDF p. 33

import Mathlib
import Definitions.Def_Arxiv2608_05214_Basic

open MeasureTheory Filter Topology
open scoped ContDiff

namespace Arxiv2608_05214

theorem one_way_decomposition (omega : ℝ) (homega : omega ≠ 0) :
    (∀ (ρ : ℝ → ℝ) (κ : ℝ → ℝ → ℝ → ℝ) (P V₁ V₂ V₃ : ℝ → ℝ → ℝ → ℂ),
      (∀ x₃, 0 < ρ x₃) → (∀ x₁ x₂ x₃, 0 < κ x₁ x₂ x₃) →
      IsFreqAcousticField omega ρ κ P V₁ V₂ V₃ →
      ∀ x₁ x₂ x₃ : ℝ,
        deriv (fun s => P x₁ x₂ s) x₃ = Complex.I * omega * ρ x₃ * V₃ x₁ x₂ x₃ ∧
        deriv (fun s => V₃ x₁ x₂ s) x₃ =
          Complex.I * omega / κ x₁ x₂ x₃ * P x₁ x₂ x₃
            - (deriv (fun s => deriv (fun s => P s x₂ x₃) s) x₁
                + deriv (fun s => deriv (fun s => P x₁ s x₃) s) x₂) / (Complex.I * omega * ρ x₃)) ∧
    (∀ ρ κ k₁ k₂ : ℝ, 0 < ρ → 0 < κ →
      let k := verticalWavenumber omega (soundSpeed ρ κ) k₁ k₂
      (∀ l : ℂ, (∃ v : Fin 2 → ℂ, v ≠ 0 ∧ (decompMatrix omega ρ κ k₁ k₂).mulVec v = l • v) ↔
          (l = Complex.I * k ∨ l = -(Complex.I * k))) ∧
      (k₁ ^ 2 + k₂ ^ 2 < omega ^ 2 / soundSpeed ρ κ ^ 2 → k.im = 0 ∧ 0 < k.re) ∧
      (omega ^ 2 / soundSpeed ρ κ ^ 2 < k₁ ^ 2 + k₂ ^ 2 → k.re = 0) ∧
      (k ≠ 0 → ∀ P V : ℝ → ℂ,
        (∀ x₃, HasDerivAt P (decompMatrix omega ρ κ k₁ k₂ 0 1 * V x₃) x₃) →
        (∀ x₃, HasDerivAt V (decompMatrix omega ρ κ k₁ k₂ 1 0 * P x₃) x₃) →
        ∀ x₃ : ℝ,
          HasDerivAt (fun z => downgoingP omega ρ k (P z) (V z))
            (Complex.I * k * downgoingP omega ρ k (P x₃) (V x₃)) x₃ ∧
          HasDerivAt (fun z => upgoingP omega ρ k (P z) (V z))
            (-(Complex.I * k) * upgoingP omega ρ k (P x₃) (V x₃)) x₃)) := by sorry

end Arxiv2608_05214
