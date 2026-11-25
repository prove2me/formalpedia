-- Prove2me | Theorems.Thm_Arxiv1510_02920_time_reversal_has_gain
-- name    : Arxiv1510_02920.time_reversal_has_gain
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T02:12:24.462341+00:00
-- url     : https://prove2.me/theorems/756cb727-cb8b-4884-afb8-58c851f25563
-- title:
--   Time reversal of the solution gives an entering wave in a material with gain at all frequencies
-- statement:
--   Let $c>0$, $a>0$, $\Omega\ne0$, and let $\varepsilon_\gamma$, $P$ and $E$ be the permittivity, the function (4) with (8), and the exiting wave (2) of the paper's example.
--
--   1. For every $\gamma>0$, real $\omega\ne0$ and $E_0\ne0$, the time-reversed field $\overline E$ solves the Helmholtz equation with the time-reversed permittivity $\overline{\varepsilon_\gamma(x,\omega)}$ at every $x$. It is everywhere the local left-going mode, $\frac{d}{dx}\overline{E(x)}=-ik_0\overline{P(x,\omega)}\,\overline{E(x)}$, and there are $T,A\ne0$ with $\overline{E(x)}e^{ik_0x}\to T$ as $x\to+\infty$ and $\overline{E(x)}e^{ik_0\overline{n_-(\omega)}x}\to A$ as $x\to-\infty$, where $n_-(\omega)=1+\Omega^2/(\gamma-i\omega)^2$. So it enters the material from the vacuum on the right without reflection: in the vacuum it is a pure left-going plane wave, and inside the material it has no counter-propagating part.
--   2. For all sufficiently large $\gamma$, the time-reversed material has gain at every frequency:
--
--   $$\operatorname{Im}\overline{\varepsilon_\gamma(x,\omega)}<0\qquad\text{for all }x\text{ and all }\omega>0,$$
--
--   violating condition (iii).
--
--   **Formalization Note** The paper asserts more generally that no modification of the solution gives a passive material reflectionless for entering waves; only its one named example, time reversal, is stated. Time reversal at real $\omega$ is complex conjugation, equivalently $\omega\mapsto-\omega$ by condition (ii).
-- source:
--   T. G. Philbin, All-frequency reflectionlessness, arXiv:1510.02920v1 (2015), claim c015; unnumbered main text, paragraph after Figure 1, PDF p. 5

import Mathlib
import Definitions.Def_Arxiv1510_02920_Basic

open Filter Topology Asymptotics

namespace Arxiv1510_02920

theorem time_reversal_has_gain (c a Om : ℝ) (hc : 0 < c) (ha : 0 < a) (hOm : Om ≠ 0) :
    (∀ γ : ℝ, 0 < γ → ∀ ω : ℝ, ω ≠ 0 → ∀ E0 : ℂ, E0 ≠ 0 →
      (∀ x, HelmholtzAt c ω (fun y => star (tanhPerm c Om a γ y (ω : ℂ)))
        (fun y => star (waveField c E0 (tanhP Om a γ) ω y)) x) ∧
      (∀ x, deriv (fun y => star (waveField c E0 (tanhP Om a γ) ω y)) x =
        -(Complex.I * ((ω / c : ℝ) : ℂ) * star (tanhP Om a γ x (ω : ℂ)) *
          star (waveField c E0 (tanhP Om a γ) ω x))) ∧
      (∃ T : ℂ, T ≠ 0 ∧ Tendsto (fun x : ℝ => star (waveField c E0 (tanhP Om a γ) ω x) *
        Complex.exp (Complex.I * ((ω / c : ℝ) : ℂ) * x)) atTop (𝓝 T)) ∧
      (∃ A : ℂ, A ≠ 0 ∧ Tendsto (fun x : ℝ => star (waveField c E0 (tanhP Om a γ) ω x) *
        Complex.exp (Complex.I * ((ω / c : ℝ) : ℂ) * star (mediumIndex Om γ ω) * x))
        atBot (𝓝 A))) ∧
    ∀ᶠ γ in atTop, ∀ x ω : ℝ, 0 < ω → (star (tanhPerm c Om a γ x (ω : ℂ))).im < 0 := by sorry

end Arxiv1510_02920
