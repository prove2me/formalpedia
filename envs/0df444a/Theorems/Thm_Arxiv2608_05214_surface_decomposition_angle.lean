-- Prove2me | Theorems.Thm_Arxiv2608_05214_surface_decomposition_angle
-- name    : Arxiv2608_05214.surface_decomposition_angle
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T19:19:33.401809+00:00
-- url     : https://prove2.me/theorems/33bd33d8-0e2f-564b-87ce-5da16d55f25f
-- title:
--   Eqs. (C-8)-(C-9): decomposition at the acquisition surface in terms of the incidence angle
-- statement:
--   At the acquisition surface $x_3=0$ let the medium be homogeneous and known, with $c_0>0$ and $\rho_0>0$. Let $\omega\ne0$, let $k_H$ be a propagating horizontal wavenumber, $|k_H|^2<\omega^2/c_0^2$, and let $k_{x_3}=\sqrt{\omega^2/c_0^2-|k_H|^2}$ and $\cos\theta=k_{x_3}/(\omega/c_0)$. Then:
--
--   1. if $\omega>0$, $\cos\theta=\sqrt{1-c_0^2|k_H|^2/\omega^2}$;
--   2. $\omega\rho_0/k_{x_3}=\rho_0c_0/\cos\theta$, so the decomposition operator $L$ acts on a plane wave at angle $\theta$ as multiplication by $\rho_0c_0/\cos\theta$;
--   3. the pressure-normalised one-way fields at the surface are
--   $$\hat P^\pm(k_H,0,\omega)=\frac12\hat P\pm\frac{\rho_0c_0}{2\cos\theta}\hat V_3;$$
--   4. at normal incidence ($k_H=0$) and $\omega>0$, $\omega\rho_0/k_{x_3}=\rho_0c_0$, the impedance relation $LV_3=\rho_0c_0V_3$.
--
--   **Formalization Note** With the principal square root in (C-7), $k_{x_3}/(\omega/c_0)$ equals $-\sqrt{1-c_0^2|k_H|^2/\omega^2}$ when $\omega<0$. Items 1 and 4 are therefore stated for $\omega>0$, and items 2 and 3, which hold for every $\omega\ne0$, use $\cos\theta=k_{x_3}c_0/\omega$. The paper's remarks on dual-sensor acquisition are not mathematical statements.
-- source:
--   H. A. Oyekan, Marchenko Theory, Algorithms, and Applications: A Review, arXiv:2608.05214v1 (2026), claim c026; Section II-B (after the operator L), PDF p. 3; Appendix C-C (Decomposition at the Acquisition Surface), eqs. (C-8)-(C-9), PDF p. 33

import Mathlib
import Definitions.Def_Arxiv2608_05214_Basic

open MeasureTheory Filter Topology
open scoped ContDiff

namespace Arxiv2608_05214

theorem surface_decomposition_angle (c₀ ρ₀ omega k₁ k₂ : ℝ) (hc₀ : 0 < c₀) (hρ₀ : 0 < ρ₀)
    (homega : omega ≠ 0) (hprop : k₁ ^ 2 + k₂ ^ 2 < omega ^ 2 / c₀ ^ 2) :
    let k := verticalWavenumber omega c₀ k₁ k₂
    let cosθ := k / ((omega : ℂ) / c₀)
    (0 < omega → cosθ = ((Real.sqrt (1 - c₀ ^ 2 * (k₁ ^ 2 + k₂ ^ 2) / omega ^ 2) : ℝ) : ℂ)) ∧
    (omega * ρ₀ : ℂ) / k = ρ₀ * c₀ / cosθ ∧
    (∀ P V : ℂ, downgoingP omega ρ₀ k P V = P / 2 + ρ₀ * c₀ / (2 * cosθ) * V ∧
      upgoingP omega ρ₀ k P V = P / 2 - ρ₀ * c₀ / (2 * cosθ) * V) ∧
    (0 < omega → k₁ = 0 → k₂ = 0 → (omega * ρ₀ : ℂ) / k = ρ₀ * c₀) := by sorry

end Arxiv2608_05214
