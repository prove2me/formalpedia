-- Prove2me | Theorems.Thm_Arxivphysics_0610143_reflection_reciprocity
-- name    : Arxivphysics_0610143.reflection_reciprocity
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T19:40:48.638159+00:00
-- url     : https://prove2.me/theorems/81421f9c-4af7-5883-9761-39a1c2a2a5c5
-- title:
--   Sec. III, last paragraph: reflection reciprocity $R_1=R_2$ ($R_\theta=R_{-\theta}$) for incidences $(k_x,k_z)$ and $(-k_x,k_z)$
-- statement:
--   Let $d>0$, $k>0$ and $|\alpha|<k$. Let $\varepsilon,\mu$ describe a reciprocal medium with a $d$-periodic object of arbitrary (asymmetric) unit cell in the slab $|z|\le h$ and vacuum outside. In TM polarization ($u=H_y$) and in TE polarization ($u=E_y$), let:
--   - $u_1$ be a field for the plane wave $e^{i(\alpha x-\beta_0z)}$ incident from above, with incident wavevector $(k_x,k_z)$;
--   - $u_2$ be a field for the mirror-image incidence $e^{i(-\alpha x-\beta_0z)}$, also from above, with incident wavevector $(-k_x,k_z)$.
--
--   Let $r^{(1)}_0$, $r^{(2)}_0$ be their zeroth-order (specularly) reflected amplitudes. Then $r^{(1)}_0=r^{(2)}_0$. Hence, for any common reference amplitude $\rho$, $|r^{(1)}_0/\rho|^2=|r^{(2)}_0/\rho|^2$, i.e. $R_1=R_2$, $R_\theta=R_{-\theta}$.
--
--   **Formalization Note** The paper normalizes by the zeroth-order amplitude with the object replaced by a perfect mirror. A planar perfect mirror at a fixed height reflects $e^{i(\pm\alpha x-\beta_0z)}$ with the same amplitude for both signs, since it depends on $\alpha$ only through $\beta_0$. This is why the reference amplitude $\rho$ is common to both incidences. The paper gives no polarization for the reflection case, so both are stated. Vacuum lies on both sides of the object.
-- source:
--   M. Iwanaga, A. S. Vengurlekar, T. Hatano, T. Ishihara, Reciprocal transmittances and reflectances: An elementary proof, arXiv:physics/0610143v4, claim c012; Sec. III, last paragraph (reflection), Fig. 4; Fig. 1(a),(c) caption, PDF p. 3

import Mathlib
import Definitions.Def_Arxivphysics_0610143_Basic

open MeasureTheory Matrix

namespace Arxivphysics_0610143

theorem reflection_reciprocity (d k h α : ℝ) (hd : 0 < d) (hk : 0 < k) (hα : |α| < k)
    (ε μ : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℂ) (hm : IsReciprocalGratingMedium d h ε μ) :
    (∀ (u₁ u₂ : ℝ × ℝ → ℂ) (r₁ t₁ r₂ t₂ : ℤ → ℂ),
      IsDownScattering d k h α (tmCoeff ε) (tmPot μ) u₁ r₁ t₁ →
      IsDownScattering d k h (-α) (tmCoeff ε) (tmPot μ) u₂ r₂ t₂ →
      r₁ 0 = r₂ 0 ∧ ∀ ρ : ℂ, ampRatioSq (r₁ 0) ρ = ampRatioSq (r₂ 0) ρ) ∧
    (∀ (u₁ u₂ : ℝ × ℝ → ℂ) (r₁ t₁ r₂ t₂ : ℤ → ℂ),
      IsDownScattering d k h α (teCoeff μ) (tePot ε) u₁ r₁ t₁ →
      IsDownScattering d k h (-α) (teCoeff μ) (tePot ε) u₂ r₂ t₂ →
      r₁ 0 = r₂ 0 ∧ ∀ ρ : ℂ, ampRatioSq (r₁ 0) ρ = ampRatioSq (r₂ 0) ρ) := by sorry

end Arxivphysics_0610143
