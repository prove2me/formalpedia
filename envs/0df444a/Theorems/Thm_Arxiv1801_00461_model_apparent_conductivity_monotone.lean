-- Prove2me | Theorems.Thm_Arxiv1801_00461_model_apparent_conductivity_monotone
-- name    : Arxiv1801_00461.model_apparent_conductivity_monotone
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:17:10.896127+00:00
-- url     : https://prove2.me/theorems/6830f75a-373e-4e9d-9472-fd0f89677a97
-- title:
--   Sec. 3.1.2: for $|\omega|^{-3/2}$ the apparent conductivity increases, for $|\omega|^{-5/2}$ it decreases
-- statement:
--   Let $\varepsilon_o>0$ and $\kappa>0$, and let $\bar\Delta\sigma_A=-\mathcal H(\bar\Delta(\omega\varepsilon_A))$ for the model $\varepsilon_A=\varepsilon_o+\kappa/|\omega|^{2+x}$. The Hilbert transforms exist for every $\omega>0$, and:
--
--   1. for $\bar\Delta\varepsilon_A\propto|\omega|^{-3/2}$ ($x=-1/2$), $\bar\Delta\sigma_A(\omega)<0$ for all $\omega>0$ and $\bar\Delta\sigma_A$ is strictly increasing on $(0,\infty)$, so the apparent conductivity increases with frequency;
--   2. for $\bar\Delta\varepsilon_A\propto|\omega|^{-5/2}$ ($x=1/2$), $\bar\Delta\sigma_A$ is strictly decreasing on $(0,\infty)$, so the apparent conductivity decreases with frequency.
--
--   **Formalization Note** The monotonicity is stated for $\bar\Delta\sigma_A$, which differs from $\sigma_A$ by the constant $\sigma_A(\infty)$. The paper's remark that the first case agrees with the measurements of Gabriel et al. is an empirical claim and is not included.
-- source:
--   Bédard and Destexhe, Kramers-Kronig relations and the properties of conductivity and permittivity in heterogeneous media, arXiv:1801.00461v1 (2018), claim c020; Sec. 3.1.2, paragraph after Case x = ±1/2, PDF p. 14

import Mathlib
import Definitions.Def_Arxiv1801_00461_Basic

open MeasureTheory Filter Topology

namespace Arxiv1801_00461

theorem model_apparent_conductivity_monotone (eps0 kappa : ℝ) (heps0 : 0 < eps0)
    (hkappa : 0 < kappa) :
    (∀ ω : ℝ, 0 < ω → (∃ v : ℝ, HasHilbert (omegaEpsDev eps0 kappa (-1 / 2)) ω v) ∧
      ∃ v : ℝ, HasHilbert (omegaEpsDev eps0 kappa (1 / 2)) ω v) ∧
    (∀ ω : ℝ, 0 < ω → appCondDevModel eps0 kappa (-1 / 2) ω < 0) ∧
    StrictMonoOn (appCondDevModel eps0 kappa (-1 / 2)) (Set.Ioi 0) ∧
    StrictAntiOn (appCondDevModel eps0 kappa (1 / 2)) (Set.Ioi 0) := by sorry

end Arxiv1801_00461
