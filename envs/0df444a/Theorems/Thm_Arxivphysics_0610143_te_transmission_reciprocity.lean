-- Prove2me | Theorems.Thm_Arxivphysics_0610143_te_transmission_reciprocity
-- name    : Arxivphysics_0610143.te_transmission_reciprocity
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T19:40:14.681206+00:00
-- url     : https://prove2.me/theorems/21ada135-a524-4f02-b19c-737ed327acb7
-- title:
--   Sec. III, polarization paragraph: transmission reciprocity $T_1=T_2$ also holds in TE polarization
-- statement:
--   Under the same assumptions as for TM polarization, consider TE polarization: $\mathbf E\parallel y$, field $u=E_y$, coefficient $A=J^{\mathsf T}\mu_{xz}^{-1}J$ and $\varepsilon_{yy}$ in place of $\mu_{yy}$. Let:
--   - $u_1$, $u_2$ be fields for the plane waves $e^{i(\alpha x-\beta_0z)}$ from above and $e^{i(-\alpha x+\beta_0z)}$ from below, with zeroth-order transmitted amplitudes $t^{(1)}_0$, $t^{(2)}_0$;
--   - $v_1$, $v_2$ be the corresponding fields without object, with amplitudes $\tau^{(1)}_0$, $\tau^{(2)}_0$.
--
--   Then $\tau^{(1)}_0=\tau^{(2)}_0$, and $|t^{(1)}_0/\tau^{(1)}_0|^2=|t^{(2)}_0/\tau^{(2)}_0|^2$, i.e. $T_1=T_2$ in TE polarization.
--
--   **Formalization Note** The paper only says the TE proof is 'similar', with the dipoles along $y$. The statement is the TE counterpart of the TM statement, in the same plane-wave setting.
-- source:
--   M. Iwanaga, A. S. Vengurlekar, T. Hatano, T. Ishihara, Reciprocal transmittances and reflectances: An elementary proof, arXiv:physics/0610143v4, claim c005; Sec. III, paragraph on TM/TE polarization, PDF pp. 2-3

import Mathlib
import Definitions.Def_Arxivphysics_0610143_Basic

open MeasureTheory Matrix

namespace Arxivphysics_0610143

theorem te_transmission_reciprocity (d k h α : ℝ) (hd : 0 < d) (hk : 0 < k) (hα : |α| < k)
    (ε μ : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℂ) (hm : IsReciprocalGratingMedium d h ε μ)
    (u₁ u₂ v₁ v₂ : ℝ × ℝ → ℂ) (r₁ t₁ r₂ t₂ ρ₁ τ₁ ρ₂ τ₂ : ℤ → ℂ)
    (h₁ : IsDownScattering d k h α (teCoeff μ) (tePot ε) u₁ r₁ t₁)
    (h₂ : IsUpScattering d k h (-α) (teCoeff μ) (tePot ε) u₂ r₂ t₂)
    (hv₁ : IsDownScattering d k h α (teCoeff vacuumTensor) (tePot vacuumTensor) v₁ ρ₁ τ₁)
    (hv₂ : IsUpScattering d k h (-α) (teCoeff vacuumTensor) (tePot vacuumTensor) v₂ ρ₂ τ₂) :
    τ₁ 0 = τ₂ 0 ∧ ampRatioSq (t₁ 0) (τ₁ 0) = ampRatioSq (t₂ 0) (τ₂ 0) := by sorry

end Arxivphysics_0610143
