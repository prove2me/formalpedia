-- Prove2me | Theorems.Thm_CondMat0408017_incoherent_drc_tmatrix_and_green
-- name    : CondMat0408017.incoherent_drc_tmatrix_and_green
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T13:23:03.664998+00:00
-- url     : https://prove2.me/theorems/4195c1d9-2e21-466c-ba85-e81d70b84df9
-- title:
--   Eq. (99) and text after eq. (100a): the incoherent mean DRC through the T-matrix, and $R=-2\pi\delta-2iG\alpha_0$
-- statement:
--   1. (eq. 99) Let $L_1$, $\omega$ and $\theta_s$ be any real numbers, $c>0$ and $\theta_0\in(-\pi/2,\pi/2)$. Let $\mathcal T$ be a random value of the T-matrix $\mathcal T(q|k)$ at a fixed off-specular pair $q\ne k$, and let $G^{(0)}(q),G^{(0)}(k)$ be constants. Then the incoherent mean DRC (60b) of the amplitude $R(q|k)=-2iG^{(0)}(q)\mathcal T(q|k)G^{(0)}(k)\alpha_0(k)$, $\alpha_0(k)=\frac\omega c\cos\theta_0$, is
--   $$\Big\langle\frac{\partial R}{\partial\theta_s}\Big\rangle_{\rm incoh}=\frac1{L_1}\frac2\pi\Big(\frac\omega c\Big)^3\cos^2\theta_s\cos\theta_0\,|G^{(0)}(q)|^2\big[\langle|\mathcal T|^2\rangle-|\langle\mathcal T\rangle|^2\big]|G^{(0)}(k)|^2 .$$
--   This $R$ is the off-specular value of (91).
--   2. (text after eq. 100a) Let $\alpha_0,G^{(0)},R^{(0)}$, $\mathcal T$ and $V$ be complex functions with $2i\alpha_0G^{(0)}+R^{(0)}=-1$ (92a) and $\mathcal T=V+VG^{(0)}\mathcal T$ (93a). Let $G(q|k)=2\pi\delta(q-k)d(k)+r(q,k)$ solve the Lippmann-Schwinger equation (100a). Assume that solutions of (100a) are unique: the homogeneous equation $h(q,k)=G^{(0)}(q)\int\frac{dp}{2\pi}V(q|p)h(p,k)$ has only $h=0$. Assume that $V(q|p)r(p,k)$ and $V(q|p)G^{(0)}(p)\mathcal T(p|k)$ are integrable in $p$. Then the amplitude of (91) is
--   $$R(q|k)=2\pi\delta(q-k)R^{(0)}(k)-2iG^{(0)}(q)\mathcal T(q|k)G^{(0)}(k)\alpha_0(k)=-2\pi\delta(q-k)-2iG(q|k)\alpha_0(k),$$
--   as an identity of the $\delta$-parts and of the regular parts.
--
--   **Formalization Note** In part 1 the $\delta$-term of (91) vanishes because $q\ne k$, and the incoherent DRC is evaluated directly from its definition (60b). In part 2 the paper says the identity "follows" from (91) and (100a). It treats $G$ as the solution of (100a), so uniqueness of that solution is made explicit as a hypothesis. The $\delta$-function terms are matched as coefficients of $2\pi\delta(q-k)$. The sentence after (99) breaks off in the source.
-- source:
--   I. Simonsen, A random walk through surface scattering phenomena: Theory and phenomenology, arXiv:cond-mat/0408017v1 (2004), claim c017; Sec. III.G-H, eq. (99) and the text after eq. (100a), PDF pp. 31-32

import Mathlib
import Definitions.Def_CondMat0408017_Basic

open MeasureTheory Filter Topology Complex

namespace CondMat0408017

theorem incoherent_drc_tmatrix_and_green {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] :
    (∀ (L1 ω c θ0 θs : ℝ) (G0q G0k : ℂ) (T : Ω → ℂ), 0 < c →
      θ0 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) →
      incoherentMeanDRC P L1 ω c θ0 θs
          (fun w => -2 * I * G0q * T w * G0k * ((ω / c * Real.cos θ0 : ℝ) : ℂ)) =
        1 / L1 * (2 / Real.pi) * (ω / c) ^ 3 * Real.cos θs ^ 2 * Real.cos θ0 * ‖G0q‖ ^ 2 *
          ((∫ w, ‖T w‖ ^ 2 ∂P) - ‖∫ w, T w ∂P‖ ^ 2) * ‖G0k‖ ^ 2) ∧
    (∀ (α0 G0 R0 : ℝ → ℂ) (Tm V : ℝ → ℝ → ℂ) (G : DKernel),
      (∀ k, 2 * I * α0 k * G0 k + R0 k = -1) →
      (∀ p k, Tm p k = V p k + ∫ q, V p q * G0 q * Tm q k / (2 * Real.pi)) →
      IsLippmannSchwinger G0 V G →
      (∀ h : ℝ → ℝ → ℂ, (∀ q k, h q k = G0 q * ∫ p, V q p * h p k / (2 * Real.pi)) → h = 0) →
      (∀ q k, Integrable (fun p => V q p * G.reg p k) ∧
        Integrable (fun p => V q p * G0 p * Tm p k)) →
      (DKernel.mk R0 (fun q k => -2 * I * G0 q * Tm q k * G0 k * α0 k) =
        DKernel.mk (fun k => -1 - 2 * I * G.diag k * α0 k)
          (fun q k => -2 * I * G.reg q k * α0 k))) := by sorry

end CondMat0408017
