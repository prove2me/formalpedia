-- Prove2me | Theorems.Thm_CondMat0408017_unitarity_energy_conservation
-- name    : CondMat0408017.unitarity_energy_conservation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T13:19:42.986796+00:00
-- url     : https://prove2.me/theorems/0681c856-394f-4e99-bfab-10bf1634a8b3
-- title:
--   Eq. (67) (as proved): the mean DRC of a non-absorbing surface integrates to one
-- statement:
--   Let a random rough surface of length $L_1>0$ be illuminated at angle $\theta_0\in(-\pi/2,\pi/2)$ with frequency $\omega>0$, and let $R(q|k)$, $k=\frac\omega c\sin\theta_0$, be the reflection amplitude of each realization, jointly measurable in the realization and $q$. Let $S(q|k)=\sqrt{\alpha_0(q)/\alpha_0(k)}\,R(q|k)$ with $\alpha_0(q)=\sqrt{\omega^2/c^2-q^2}$. Assume that almost every realization satisfies (eq. 66)
--
--   $$\frac1{L_1}\int_{-\omega/c}^{\omega/c}\frac{dq}{2\pi}\,|S(q|k)|^2=1 .$$
--
--   Then the mean differential reflection coefficient (58) satisfies (eq. 67)
--
--   $$\int_{-\pi/2}^{\pi/2}\Big\langle\frac{\partial R}{\partial\theta_s}\Big\rangle d\theta_s=1 .$$
--
--   **Formalization Note** The paper obtains (66) from the unitarity relation (65), $\int\frac{dq}{2\pi}S(q|k)S^*(q|k')=2\pi\delta(k-k')$, by integrating over a momentum interval of width $2\pi/L_1$, that is, by identifying $2\pi\delta(0)$ with $L_1$. That step is heuristic and has no precise counterpart, so (66) is the hypothesis. The statement is the step "(66) with (58) and $q=\frac\omega c\sin\theta_s$ gives (67)", hence "as proved".
-- source:
--   I. Simonsen, A random walk through surface scattering phenomena: Theory and phenomenology, arXiv:cond-mat/0408017v1 (2004), claim c008; Sec. III.D.2, eqs. (66)-(67) [Theory:Eq:meanDRC-conservation] with eqs. (58), (63), PDF p. 22

import Mathlib
import Definitions.Def_CondMat0408017_Basic

open MeasureTheory Filter Topology Complex

namespace CondMat0408017

theorem unitarity_energy_conservation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (L1 ω c θ0 : ℝ) (hL1 : 0 < L1) (hω : 0 < ω) (hc : 0 < c)
    (hθ0 : θ0 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) (R : Ω → ℝ → ℂ)
    (hR : Measurable (Function.uncurry R))
    (h66 : ∀ᵐ w ∂P, 1 / L1 * ∫ q in (-(ω / c))..(ω / c),
        ‖sMatrixRad (ω / c) (ω / c * Real.sin θ0) (R w) q‖ ^ 2 / (2 * Real.pi) = 1) :
    ∫ θs in (-(Real.pi / 2))..(Real.pi / 2),
        meanDRC P L1 ω c θ0 θs (fun w => R w (ω / c * Real.sin θs)) = 1 := by sorry

end CondMat0408017
