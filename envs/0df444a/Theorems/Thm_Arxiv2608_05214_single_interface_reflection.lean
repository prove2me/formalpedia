-- Prove2me | Theorems.Thm_Arxiv2608_05214_single_interface_reflection
-- name    : Arxiv2608_05214.single_interface_reflection
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T19:17:21.08227+00:00
-- url     : https://prove2.me/theorems/5603125c-51b8-5f2e-a6bf-0eae211e4c4e
-- title:
--   Eqs. (29)-(30): reflection coefficient of a single interface
-- statement:
--   Let $f:\mathbb R\to\mathbb R$ be a differentiable waveform with $f'\not\equiv0$, and let an interface at traveltime $\tau_0$ separate two homogeneous half-spaces. Above the interface the scaled field is $\psi=f(t-\tau)+r\,f(t+\tau-2\tau_0)$: an incident wave and its reflection, which at $\tau=0$ is the response $r\,f(t-2\tau_0)$ of $R(t)=r\,\delta(t-2\tau_0)$. Below the interface $\psi=T\,f(t-\tau)$. Impose continuity at $\tau_0$ of the displacement $u=\psi/\eta$ and of the traction $\eta^2\,\partial_\tau u$.
--
--   1. For any scalings $\eta_1,\eta_2>0$ ($\psi=\eta u$), the interface conditions can be met with $r=(\eta_1^2-\eta_2^2)/(\eta_1^2+\eta_2^2)$, and any $r,T$ meeting them satisfy
--   $$r=\frac{\eta_1^2-\eta_2^2}{\eta_1^2+\eta_2^2},\qquad \frac{\eta_2^2}{\eta_1^2}=\frac{1-r}{1+r}.$$
--   With the paper's displacement scaling $\eta_i^2=Z_i=\rho_ic_i$ this reads $r=(Z_1-Z_2)/(Z_1+Z_2)$ and $Z_2/Z_1=(1-r)/(1+r)$ (eq. 30).
--   2. With the scaling $\eta_i=Z_i^{-1/2}$ (the derivation run on pressure), any $r,T$ meeting the conditions satisfy $r=(Z_2-Z_1)/(Z_2+Z_1)$.
--
--   **Formalization Note** The spike $R(t)=r\,\delta(t-2\tau_0)$ is represented by its response to an arbitrary differentiable waveform $f$. The sentence that solving the GLM equation with this $R$ recovers the impedance contrast is asserted in the paper without proof and is not part of the statement.
-- source:
--   H. A. Oyekan, Marchenko Theory, Algorithms, and Applications: A Review, arXiv:2608.05214v1 (2026), claim c007; Section III-E (Reconstruction of Medium Properties), eqs. (29)-(30), PDF p. 7

import Mathlib
import Definitions.Def_Arxiv2608_05214_Basic

open MeasureTheory Filter Topology
open scoped ContDiff

namespace Arxiv2608_05214

theorem single_interface_reflection (τ₀ : ℝ) (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hf' : ∃ s, deriv f s ≠ 0) :
    (∀ η₁ η₂ : ℝ, 0 < η₁ → 0 < η₂ →
      (∃ T, SatisfiesInterfaceConditions η₁ η₂ τ₀ f ((η₁ ^ 2 - η₂ ^ 2) / (η₁ ^ 2 + η₂ ^ 2)) T) ∧
      ∀ r T, SatisfiesInterfaceConditions η₁ η₂ τ₀ f r T →
        r = (η₁ ^ 2 - η₂ ^ 2) / (η₁ ^ 2 + η₂ ^ 2) ∧ η₂ ^ 2 / η₁ ^ 2 = (1 - r) / (1 + r)) ∧
    (∀ Z₁ Z₂ : ℝ, 0 < Z₁ → 0 < Z₂ → ∀ r T,
      SatisfiesInterfaceConditions (1 / Real.sqrt Z₁) (1 / Real.sqrt Z₂) τ₀ f r T →
        r = (Z₂ - Z₁) / (Z₂ + Z₁)) := by sorry

end Arxiv2608_05214
