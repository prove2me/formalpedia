-- Prove2me | Theorems.Thm_Arxivphysics_0610143_tm_zeroth_order_amplitudes_equal
-- name    : Arxivphysics_0610143.tm_zeroth_order_amplitudes_equal
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T19:39:01.990543+00:00
-- url     : https://prove2.me/theorems/23bb7df5-b24d-58ef-baba-345f5045f894
-- title:
--   Sec. III, Eq. (7): the zeroth-order transmitted amplitudes of the two reciprocal TM incidences are equal
-- statement:
--   Let $d>0$, $k>0$ and $|\alpha|<k$. Let $\varepsilon,\mu$ describe a reciprocal medium with a $d$-periodic object in the slab $|z|\le h$ and vacuum outside, as in the definitions. Consider TM polarization ($u=H_y$). Let:
--   - $u_1$ be a field for the unit plane wave $e^{i(\alpha x-\beta_0z)}$ incident from above, with zeroth-order transmitted amplitude $t^{(1)}_0$ (the coefficient of $e^{i(\alpha x-\beta_0z)}$ below the object);
--   - $u_2$ be a field for the reversed incidence, the unit plane wave $e^{i(-\alpha x+\beta_0z)}$ from below, with zeroth-order transmitted amplitude $t^{(2)}_0$ (the coefficient of $e^{i(-\alpha x+\beta_0z)}$ above the object).
--
--   Then $t^{(1)}_0=t^{(2)}_0$. That is, the zeroth harmonic of each field, observed on the far side where the other source sits, has the same amplitude (Eq. (7), $E_1^{(0)}=E_2^{(0)}$).
--
--   **Formalization Note** The paper derives Eq. (7) for two identical finite dipole arrays from the approximate Eq. (5c) and the reciprocal theorem. It is stated here in the plane-wave limit, with equal (unit) incident amplitudes. The paper's $E_i^{(0)}$ are moduli; the statement asserts equality of the complex amplitudes, which is stronger. No uniqueness of the scattering problem is assumed; the conclusion holds for every pair of such fields.
-- source:
--   M. Iwanaga, A. S. Vengurlekar, T. Hatano, T. Ishihara, Reciprocal transmittances and reflectances: An elementary proof, arXiv:physics/0610143v4, claim c002; Sec. III, Eq. (7) (tex label E_reci), with Eqs. (1), (4), (5c), Fig. 3, PDF p. 2

import Mathlib
import Definitions.Def_Arxivphysics_0610143_Basic

open MeasureTheory Matrix

namespace Arxivphysics_0610143

theorem tm_zeroth_order_amplitudes_equal (d k h α : ℝ) (hd : 0 < d) (hk : 0 < k) (hα : |α| < k)
    (ε μ : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℂ) (hm : IsReciprocalGratingMedium d h ε μ)
    (u₁ u₂ : ℝ × ℝ → ℂ) (r₁ t₁ r₂ t₂ : ℤ → ℂ)
    (h₁ : IsDownScattering d k h α (tmCoeff ε) (tmPot μ) u₁ r₁ t₁)
    (h₂ : IsUpScattering d k h (-α) (tmCoeff ε) (tmPot μ) u₂ r₂ t₂) :
    t₁ 0 = t₂ 0 := by sorry

end Arxivphysics_0610143
