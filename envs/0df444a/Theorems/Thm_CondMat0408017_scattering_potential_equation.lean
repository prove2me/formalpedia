-- Prove2me | Theorems.Thm_CondMat0408017_scattering_potential_equation
-- name    : CondMat0408017.scattering_potential_equation
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-26T13:22:05.334037+00:00
-- url     : https://prove2.me/theorems/83f3399d-ba4a-57de-83cb-479b2e0a134b
-- title:
--   Eqs. (94)-(95): the T-matrix equation and the integral equation for the scattering potential
-- statement:
--   Let $N^\pm(p|q)$, $\alpha_0,G^{(0)},R^{(0)}$, $\mathcal T(q|k)$ and $V(q|k)$ be complex functions. Assume that $2i\alpha_0(k)G^{(0)}(k)+R^{(0)}(k)=-1$ (eq. 92a). Assume also that the amplitude postulated in (91), $R(q|k)=2\pi\delta(q-k)R^{(0)}(k)-2iG^{(0)}(q)\mathcal T(q|k)G^{(0)}(k)\alpha_0(k)$, satisfies the reduced Rayleigh equation $\int\frac{dq}{2\pi}N^+(p|q)R(q|k)=N^-(p|k)$ for all $p,k$. Then:
--
--   1. (eq. 94) For $\alpha_0(k)\ne0$ and $G^{(0)}(k)\ne0$,
--   $$\int\frac{dq}{2\pi}N^+(p|q)G^{(0)}(q)\mathcal T(q|k)=\frac{R^{(0)}(k)N^+(p|k)-N^-(p|k)}{2i\alpha_0(k)G^{(0)}(k)} .$$
--   2. For $\alpha_0(q)\ne0$, the two expressions for $A$ agree:
--   $$\frac{[2i\alpha_0(q)G^{(0)}(q)+R^{(0)}(q)]N^+(p|q)-N^-(p|q)}{2i\alpha_0(q)}=-\frac{N^+(p|q)+N^-(p|q)}{2i\alpha_0(q)}=A(p|q) .$$
--   3. (eq. 95) Assume moreover $\mathcal T(q|k)=V(q|k)+\int\frac{dp}{2\pi}\mathcal T(q|p)G^{(0)}(p)V(p|k)$ (eq. 93b). Fix $p,k$ with $\alpha_0(k),G^{(0)}(k)\ne0$, and assume $\alpha_0(q),G^{(0)}(q)\ne0$ for almost every $q$. Assume that $N^+(p|q)G^{(0)}(q)V(q|k)$ and $N^+(p|q)G^{(0)}(q)\mathcal T(q|k)$ are integrable in $q$, and that $N^+(p|q')G^{(0)}(q')\mathcal T(q'|q)G^{(0)}(q)V(q|k)$ is integrable in $(q,q')$. Then
--   $$\int\frac{dq}{2\pi}A(p|q)V(q|k)=B(p|k),\qquad B(p|k)=\frac{R^{(0)}(k)N^+(p|k)-N^-(p|k)}{2i\alpha_0(k)G^{(0)}(k)} .$$
--
--   **Formalization Note** The postulate (91) and the T-matrix equation (93) are quoted from Brown et al. (1984) and are hypotheses. The $\delta$-term of (91) acts in the Rayleigh equation through $\int\frac{dq}{2\pi}N^+(p|q)2\pi\delta(q-k)R^{(0)}(k)=N^+(p|k)R^{(0)}(k)$. The paper says it uses (93a). The derivation closes with (93b), $\mathcal T=V+\mathcal TG^{(0)}V$, which the paper states is equivalent by reciprocity, so (93b) is the hypothesis. Corrections of misprints: in (94) $N^+(p|k)$, printed $N^+(q|k)$; in the first form of $A$ the denominator $2i\alpha_0(q)$, printed $2i\alpha_0(k)$; in (95c) $R^{(0)}(k)$, printed $R^{(0)}(p)$. The integrability conditions make the interchange of integrals in the derivation legitimate.
-- source:
--   I. Simonsen, A random walk through surface scattering phenomena: Theory and phenomenology, arXiv:cond-mat/0408017v1 (2004), claim c039; Sec. III.G.2, eqs. (Theory:T-matrix-eq), (Theory:int-eq-scattering-pot:total) [(94)-(95)] from eqs. (91), (92a), (93b), PDF p. 30

import Mathlib
import Definitions.Def_CondMat0408017_Basic

open MeasureTheory Filter Topology Complex

namespace CondMat0408017

theorem scattering_potential_equation (Np Nm : ℝ → ℝ → ℂ) (α0 G0 R0 : ℝ → ℂ)
    (Tm V : ℝ → ℝ → ℂ)
    (hRRE : ∀ p k, DKernel.applyLeft Np
        ⟨R0, fun q k => -2 * I * G0 q * Tm q k * G0 k * α0 k⟩ p k = Nm p k)
    (h92 : ∀ k, 2 * I * α0 k * G0 k + R0 k = -1) :
    (∀ p k, α0 k ≠ 0 → G0 k ≠ 0 →
      ∫ q, Np p q * G0 q * Tm q k / (2 * Real.pi) =
        (R0 k * Np p k - Nm p k) / (2 * I * α0 k * G0 k)) ∧
    (∀ p q, α0 q ≠ 0 →
      ((2 * I * α0 q * G0 q + R0 q) * Np p q - Nm p q) / (2 * I * α0 q) =
        -(Np p q + Nm p q) / (2 * I * α0 q)) ∧
    ((∀ q k, Tm q k = V q k + ∫ p, Tm q p * G0 p * V p k / (2 * Real.pi)) →
      ∀ p k, α0 k ≠ 0 → G0 k ≠ 0 → (∀ᵐ q, α0 q ≠ 0 ∧ G0 q ≠ 0) →
        Integrable (fun q => Np p q * G0 q * V q k) →
        Integrable (fun q => Np p q * G0 q * Tm q k) →
        Integrable (Function.uncurry fun q q' => Np p q' * G0 q' * Tm q' q * G0 q * V q k) →
        ∫ q, -(Np p q + Nm p q) / (2 * I * α0 q) * V q k / (2 * Real.pi) =
          (R0 k * Np p k - Nm p k) / (2 * I * α0 k * G0 k)) := by sorry

end CondMat0408017
