-- Prove2me | Theorems.Thm_Arxiv1510_02920_entering_type_with_plasma_condition
-- name    : Arxiv1510_02920.entering_type_with_plasma_condition
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T02:13:30.650045+00:00
-- url     : https://prove2.me/theorems/beecef47-4bfa-454d-a44c-65c659a5608a
-- title:
--   Entering-type all-frequency reflectionless permittivities exist when (iv) allows a $1/\omega^2$ divergence
-- statement:
--   Let $c>0$. There are a function $P(x,\omega)$ and limits $g_+(\omega)$ with the following properties.
--
--   1. For every real $\omega\ne0$, $P(\cdot,\omega)$ is differentiable, $P(x,\omega)\to1$ as $x\to-\infty$ (vacuum on the left), $P(x,\omega)\to g_+(\omega)$ as $x\to+\infty$, and $\partial_xP(x,\omega)\to0$ as $x\to\pm\infty$.
--   2. $g_+(\omega)^2\ne1$ for some $\omega\ne0$, so the right side is not vacuum.
--   3. The permittivity $\varepsilon=P^2-(ic/\omega)\partial_xP$ satisfies conditions (i), (ii), (iii) and (v), and condition (iv) relaxed to allow a $1/\omega^2$ divergence ($n\ge-2$).
--
--   By eq. (3), the right-going wave (2) then enters this material from the vacuum on the left without reflection, at every frequency.
--
--   **Formalization Note** The paper says only that such "entering" solutions "exist and are not difficult to find using the method above" and gives no example. The statement asserts existence within that method, the ansatz (2)-(3). The paper's remark that ordinary metals and dielectrics cannot realise these solutions is not formalized.
-- source:
--   T. G. Philbin, All-frequency reflectionlessness, arXiv:1510.02920v1 (2015), claim c011; unnumbered main text, paragraph before Figure 2, PDF p. 5

import Mathlib
import Definitions.Def_Arxiv1510_02920_Basic

open Filter Topology Asymptotics

namespace Arxiv1510_02920

theorem entering_type_with_plasma_condition (c : ℝ) (hc : 0 < c) :
    ∃ (P : ℝ → ℂ → ℂ) (gp : ℝ → ℂ),
      (∀ ω : ℝ, ω ≠ 0 →
        Differentiable ℝ (fun x : ℝ => P x (ω : ℂ)) ∧
        Tendsto (fun x : ℝ => P x (ω : ℂ)) atBot (𝓝 1) ∧
        Tendsto (fun x : ℝ => P x (ω : ℂ)) atTop (𝓝 (gp ω)) ∧
        Tendsto (fun x : ℝ => deriv (fun y : ℝ => P y (ω : ℂ)) x) atBot (𝓝 0) ∧
        Tendsto (fun x : ℝ => deriv (fun y : ℝ => P y (ω : ℂ)) x) atTop (𝓝 0)) ∧
      (∃ ω : ℝ, ω ≠ 0 ∧ gp ω ^ 2 ≠ 1) ∧
      CondAnalytic (perm c P) ∧ CondReality (perm c P) ∧ CondNoGain (perm c P) ∧
      CondLowFreq (-2) (perm c P) ∧ CondHighFreq (perm c P) := by sorry

end Arxiv1510_02920
