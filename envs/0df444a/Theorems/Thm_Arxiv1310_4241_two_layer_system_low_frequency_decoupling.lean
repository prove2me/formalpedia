-- Prove2me | Theorems.Thm_Arxiv1310_4241_two_layer_system_low_frequency_decoupling
-- name    : Arxiv1310_4241.two_layer_system_low_frequency_decoupling
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T11:26:41.366399+00:00
-- url     : https://prove2.me/theorems/999c2ead-825a-46fa-aaaf-c807e460dbd9
-- title:
--   Eq. (53): the two-layer system has the block form $\begin{pmatrix}A_{11}&\omega A_{12}\\\omega A_{21}&A_{22}\end{pmatrix}$ and decouples stably as $\omega\to0$
-- statement:
--   Let $\varepsilon_0,\mu_0,\varepsilon_1,\mu_1>0$ and $(\xi,\eta)\ne(0,0)$. For $\omega>0$ let $M(\omega)$ be the $4\times4$ matrix of the system (53): its entries are the Fourier coefficients of the jumps $[\mathcal S_0\nabla\cdot\mathbf E]$, $[\mathbf n\cdot\varepsilon\mathbf E]$, $[\mathcal S_0\nabla\cdot\mathbf H]$, $[\mathbf n\cdot\mu\mathbf H]$ across $z=0$ produced by unit sources $\widehat r_0,\widehat r_1,\widehat q_0,\widehat q_1$ of the two-layer generalized Debye representation (45)-(48), with $[f]=f_0-f_1$. Then there are $2\times2$ blocks $A_{ij}(\omega)$, defined for $\omega\ge0$ and continuous at $\omega=0$ (within $\omega\ge0$), with
--
--   $$M(\omega)=\begin{pmatrix}A_{11}(\omega)&\omega A_{12}(\omega)\\ \omega A_{21}(\omega)&A_{22}(\omega)\end{pmatrix}\qquad(\omega>0),$$
--
--   $A_{11}(0)$ and $A_{22}(0)$ are invertible, $M(\omega)$ is invertible for all small $\omega>0$, and for every right-hand side $b$ the solution converges:
--
--   $$M(\omega)^{-1}b\to\begin{pmatrix}A_{11}(0)^{-1}&0\\0&A_{22}(0)^{-1}\end{pmatrix}b\qquad(\omega\to0^+).$$
--
--   So no instability arises in $A_{11}$ or $A_{22}$ as $\omega\to0$, the coupling between the $\widehat r_j$ and the $\widehat q_j$ vanishes, and in the limit $\widehat r_0,\widehat r_1$ depend only on the electric data and $\widehat q_0,\widehat q_1$ only on the magnetic data.
--
--   **Formalization Note** The paper does not print the blocks $A_{ij}$ or the orientation of the jump; the matrix is computed from the representation itself, and the orientation does not affect the conclusions. "Stable as $\omega\to0$" is stated as continuity of the blocks at $\omega=0$ together with invertibility of the limits. One Fourier mode, positive real material constants.
-- source:
--   M. O'Neil, A generalized Debye source approach to electromagnetic scattering in layered media, arXiv:1310.4241v1 (2013), claim c019; Section V.B, eq. (53) and the following paragraph, PDF pp. 12-13; transmission conditions eq. (51), PDF p. 12

import Mathlib
import Definitions.Def_Arxiv1310_4241_Basic

open MeasureTheory Filter Topology

namespace Arxiv1310_4241

theorem two_layer_system_low_frequency_decoupling (ε0 μ0 ε1 μ1 : ℝ) (hε0 : 0 < ε0)
    (hμ0 : 0 < μ0) (hε1 : 0 < ε1) (hμ1 : 0 < μ1) (ξ η : ℝ) (hξη : (ξ, η) ≠ (0, 0)) :
    ∃ A₁₁ A₁₂ A₂₁ A₂₂ : ℝ → Matrix (Fin 2) (Fin 2) ℂ,
      (∀ ω : ℝ, 0 < ω → twoLayerSystem ω ε0 μ0 ε1 μ1 ξ η =
        Matrix.fromBlocks (A₁₁ ω) ((ω : ℂ) • A₁₂ ω) ((ω : ℂ) • A₂₁ ω) (A₂₂ ω)) ∧
      ContinuousWithinAt A₁₁ (Set.Ici 0) 0 ∧ ContinuousWithinAt A₁₂ (Set.Ici 0) 0 ∧
      ContinuousWithinAt A₂₁ (Set.Ici 0) 0 ∧ ContinuousWithinAt A₂₂ (Set.Ici 0) 0 ∧
      IsUnit (A₁₁ 0).det ∧ IsUnit (A₂₂ 0).det ∧
      (∀ᶠ ω in 𝓝[>] (0 : ℝ), IsUnit (twoLayerSystem ω ε0 μ0 ε1 μ1 ξ η).det) ∧
      ∀ b : Fin 2 ⊕ Fin 2 → ℂ,
        Tendsto (fun ω : ℝ => Matrix.mulVec (twoLayerSystem ω ε0 μ0 ε1 μ1 ξ η)⁻¹ b) (𝓝[>] 0)
          (𝓝 (Matrix.mulVec (Matrix.fromBlocks (A₁₁ 0)⁻¹ 0 0 (A₂₂ 0)⁻¹) b)) := by sorry

end Arxiv1310_4241
