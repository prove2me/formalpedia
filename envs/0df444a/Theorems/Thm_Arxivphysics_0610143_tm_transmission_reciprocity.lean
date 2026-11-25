-- Prove2me | Theorems.Thm_Arxivphysics_0610143_tm_transmission_reciprocity
-- name    : Arxivphysics_0610143.tm_transmission_reciprocity
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T19:39:34.366836+00:00
-- url     : https://prove2.me/theorems/a0c1b3e0-b901-5333-aee0-e10c01afea0c
-- title:
--   Sec. III, Eqs. (8)-(9): transmission reciprocity $T_1=T_2$ ($T_{\mathbf k}=T_{-\mathbf k}$) for a one-dimensionally periodic object in TM polarization
-- statement:
--   Let $d>0$, $k>0$ and $|\alpha|<k$. Let $\varepsilon,\mu$ describe a reciprocal medium (symmetric, possibly absorbing tensors) with a $d$-periodic object of arbitrary unit cell in the slab $|z|\le h$ and vacuum outside. Consider TM polarization ($u=H_y$).
--   - Let $u_1$ be a field for the plane wave $e^{i(\alpha x-\beta_0z)}$ incident from above, with zeroth-order transmitted amplitude $t^{(1)}_0$.
--   - Let $u_2$ be a field for the reversed incidence $(k_x,k_z)\to(-k_x,-k_z)$, the plane wave $e^{i(-\alpha x+\beta_0z)}$ from below, with zeroth-order transmitted amplitude $t^{(2)}_0$.
--   - Let $v_1$, $v_2$ be the corresponding fields with no object ($\varepsilon=\mu=1$ everywhere), with zeroth-order transmitted amplitudes $\tau^{(1)}_0$, $\tau^{(2)}_0$.
--
--   Then $\tau^{(1)}_0=\tau^{(2)}_0$ (Eq. (8)), and the transmittances $T_i=|t^{(i)}_0/\tau^{(i)}_0|^2$ of Eq. (9) are equal: $T_1=T_2$, i.e. $T_{\mathbf k}=T_{-\mathbf k}$.
--
--   **Formalization Note** As in the definitions, this is the plane-wave limit of the paper's dipole-array configuration (Fig. 3). Only the zeroth (undiffracted) order is compared. The media on both sides of the object are vacuum, as in the paper's derivation. The quartz substrate of the paper's sample (Sec. IV) is not covered.
-- source:
--   M. Iwanaga, A. S. Vengurlekar, T. Hatano, T. Ishihara, Reciprocal transmittances and reflectances: An elementary proof, arXiv:physics/0610143v4, claim c003; Sec. III, Eqs. (8), (9) (tex labels E0_reci, T_reci) and the relation T_1 = T_2; Fig. 1(a),(b) caption, PDF p. 2

import Mathlib
import Definitions.Def_Arxivphysics_0610143_Basic

open MeasureTheory Matrix

namespace Arxivphysics_0610143

theorem tm_transmission_reciprocity (d k h α : ℝ) (hd : 0 < d) (hk : 0 < k) (hα : |α| < k)
    (ε μ : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℂ) (hm : IsReciprocalGratingMedium d h ε μ)
    (u₁ u₂ v₁ v₂ : ℝ × ℝ → ℂ) (r₁ t₁ r₂ t₂ ρ₁ τ₁ ρ₂ τ₂ : ℤ → ℂ)
    (h₁ : IsDownScattering d k h α (tmCoeff ε) (tmPot μ) u₁ r₁ t₁)
    (h₂ : IsUpScattering d k h (-α) (tmCoeff ε) (tmPot μ) u₂ r₂ t₂)
    (hv₁ : IsDownScattering d k h α (tmCoeff vacuumTensor) (tmPot vacuumTensor) v₁ ρ₁ τ₁)
    (hv₂ : IsUpScattering d k h (-α) (tmCoeff vacuumTensor) (tmPot vacuumTensor) v₂ ρ₂ τ₂) :
    τ₁ 0 = τ₂ 0 ∧ ampRatioSq (t₁ 0) (τ₁ 0) = ampRatioSq (t₂ 0) (τ₂ 0) := by sorry

end Arxivphysics_0610143
