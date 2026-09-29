-- Prove2me | Theorems.Thm_DSSYKScales_fermion_two_point_cosmic_units
-- name    : DSSYKScales.fermion_two_point_cosmic_units
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T01:59:04.374844+00:00
-- url     : https://prove2.me/theorems/cbaaa45b-1e7a-45f8-bf7e-92bdf6b9c4ac
-- title:
--   Single-fermion correlator is sensible in cosmic units: $\cosh^{-2/q}(\mathcal J q t_c)\to e^{-2|\mathcal J||t_c|}$
-- statement:
--   Let $q_n\to\infty$ and let $\mathcal J,t_c\in\mathbb R$. With string time $t_s=q_n t_c$, the large-$q$ single-fermion correlator $G(t_s)=\bigl(1/\cosh^2\mathcal J t_s\bigr)^{1/q}$ (eq. (9.3)) satisfies
--   $$\lim_{n\to\infty}\Bigl(\frac{1}{\cosh^2(\mathcal J\,q_n t_c)}\Bigr)^{1/q_n}=e^{-2|\mathcal J|\,|t_c|}.$$
--
--   This is the precise form of (9.4), $\langle\chi(0)\chi(t_c)\rangle\sim e^{-\mathcal J|t_c|}$. Written in string units the correlator (9.3) is not sensible (it tends to $1$ at fixed $t_s$). In cosmic units it has a finite, $q$-independent decay on the cosmic scale $L_c\sim1/\mathcal J$. The paper uses this to argue that most fermions stay near the horizon.
--
--   **Formalization Note** The paper writes the decay as $e^{-\mathcal J|t_c|}$ with "$\sim$". The exact limit of (9.3) is $e^{-2\mathcal J|t_c|}$ for $\mathcal J>0$. The statement allows any real $\mathcal J$ (hence $|\mathcal J|$). Only $q_n\to\infty$ is assumed, and $N$ plays no role.
-- source:
--   L. Susskind, "De Sitter Space, Double-Scaled SYK, and the Separation of Scales in the Semiclassical Limit", arXiv:2209.09999v1 [hep-th] (2022), https://arxiv.org/abs/2209.09999, Section 9.1 (DSSYK$_\infty$ Correlator), p. 40, eqs. (9.3)-(9.4)

import Mathlib
import Definitions.Def_DSSYKScales_defs

open Filter Topology

namespace DSSYKScales
theorem fermion_two_point_cosmic_units (q : ℕ → ℕ) (J tc : ℝ)
    (hq : Tendsto (fun n => (q n : ℝ)) atTop atTop) :
    Tendsto (fun n => (1 / Real.cosh (J * ((q n : ℝ) * tc)) ^ 2) ^ (1 / (q n : ℝ)))
      atTop (𝓝 (Real.exp (-(2 * |J| * |tc|)))) := by sorry
end DSSYKScales
