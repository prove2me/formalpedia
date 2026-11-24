-- Prove2me | Theorems.Thm_Arxiv1801_00461_admittance_variation_phase
-- name    : Arxiv1801_00461.admittance_variation_phase
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:11:59.947829+00:00
-- url     : https://prove2.me/theorems/63972744-5701-4f0b-a025-89ee400e1774
-- title:
--   Eqs. (31)-(32): the phase of the admittance variation
-- statement:
--   Under the hypotheses of eq. (30), for every real $\omega$ (eq. (31))
--
--   $$\bar\Delta\gamma(\omega)=\bar\Delta\gamma'(\omega)+i\,\mathcal H(\bar\Delta\gamma')(\omega),$$
--
--   and wherever $\bar\Delta\gamma'(\omega)\ne0$ the phase $\phi=\arg\bar\Delta\gamma(\omega)$ satisfies (eq. (32))
--
--   $$\tan\phi=\frac{\mathcal H(\bar\Delta\gamma')(\omega)}{\bar\Delta\gamma'(\omega)} .$$
--
--   The phase of the admittance variation is thus fixed by its real part.
--
--   **Formalization Note** The tangent formula is stated where its denominator is non-zero.
-- source:
--   Bédard and Destexhe, Kramers-Kronig relations and the properties of conductivity and permittivity in heterogeneous media, arXiv:1801.00461v1 (2018), claim c009; Sec. 2.4, eqs. (31)-(32), PDF p. 10

import Mathlib
import Definitions.Def_Arxiv1801_00461_Basic

open MeasureTheory Filter Topology

namespace Arxiv1801_00461

theorem admittance_variation_phase (sigInf : ℝ → ℂ) (dsig : ℝ → ℝ) (hdsig : IntegrableOn dsig (Set.Ioi 0))
    (eps0 : ℝ) (heps0 : 0 < eps0) (chi : ℝ → ℝ) (hchi : IntegrableOn chi (Set.Ioi 0))
    (hdecay : Tendsto (fun a : ℝ => (a : ℂ) * permDev eps0 chi a) (cocompact ℝ) (𝓝 0)) :
    (∀ ω : ℝ, admDev sigInf dsig eps0 chi ω =
        ((admDev sigInf dsig eps0 chi ω).re : ℂ) + Complex.I * hilbert (fun a => (admDev sigInf dsig eps0 chi a).re) ω) ∧
    (∀ ω : ℝ, (admDev sigInf dsig eps0 chi ω).re ≠ 0 →
      Real.tan (Complex.arg (admDev sigInf dsig eps0 chi ω)) =
        hilbert (fun a => (admDev sigInf dsig eps0 chi a).re) ω / (admDev sigInf dsig eps0 chi ω).re) := by sorry

end Arxiv1801_00461
