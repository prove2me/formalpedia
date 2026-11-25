-- Prove2me | Theorems.Thm_Arxiv1707_02146_cross_term_decay_time_halved
-- name    : Arxiv1707_02146.cross_term_decay_time_halved
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T00:25:08.061528+00:00
-- url     : https://prove2.me/theorems/e8a81bb6-3ac2-46bf-8055-ec3f66dacc2c
-- title:
--   p. 3, the ratio of 2: the cross term of two speckles decaying as $e^{-t/\tau_m}$ decays with time $\tau_m/2$
-- statement:
--   Let $\tau_m>0$ and let $r,s:\mathbb{R}\to\mathbb{R}$ be the averaged time-of-flight profiles of the reference and the modulated broadband speckles, each decaying as $\propto e^{-t/\tau_m}$: $r(t)=C_r e^{-t/\tau_m}$ and $s(t)=C_s e^{-t/\tau_m}$ for $t\ge0$, with $C_r,C_s\neq0$. Then their cross term decays as
--   $$r(t)\,s(t)=C\,e^{-2t/\tau_m}\qquad(t\ge0)$$
--   for a constant $C\neq0$. Its decay time is $\tau_m/2$, and $\tau_m/2$ is the only $\tau>0$ for which $r(t)s(t)\propto e^{-t/\tau}$ on $t\ge0$.
--
--   The paper identifies this decay time with the average temporal duration $\tau_f$ at the focus, giving $\tau_f\simeq\tau_m/2$.
--
--   **Formalization Note** The statement covers the mathematical step of the paper's argument. The physical identification of the focus duration with the decay time of the cross term, and the use of averaged profiles, are the paper's modelling assumptions and are not part of the statement.
-- source:
--   Mounaix, de Aguiar and Gigan, Temporal recompression through a scattering medium via a broadband transmission matrix, arXiv:1707.02146v1 (2017), claim c005; main text, paragraph after the main result ("This ratio of 2 can be easily understood"), PDF p. 3

import Mathlib
import Definitions.Def_Arxiv1707_02146_Basic

open Matrix ComplexConjugate

namespace Arxiv1707_02146

theorem cross_term_decay_time_halved (r s : ℝ → ℝ) (τm : ℝ)
    (hr : HasExpDecay r τm) (hs : HasExpDecay s τm) :
    (∃ C : ℝ, C ≠ 0 ∧ ∀ t : ℝ, 0 ≤ t → r t * s t = C * Real.exp (-2 * t / τm)) ∧
    HasExpDecay (fun t => r t * s t) (τm / 2) ∧
    ∀ τf : ℝ, HasExpDecay (fun t => r t * s t) τf → τf = τm / 2 := by sorry

end Arxiv1707_02146
