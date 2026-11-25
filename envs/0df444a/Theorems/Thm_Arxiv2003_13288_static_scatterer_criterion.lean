-- Prove2me | Theorems.Thm_Arxiv2003_13288_static_scatterer_criterion
-- name    : Arxiv2003_13288.static_scatterer_criterion
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T08:50:29.59485+00:00
-- url     : https://prove2.me/theorems/0a6fb8c5-c287-5298-8ab8-dbad52400e91
-- title:
--   Sec. 3, postulation (2): the criterion for treating moving scatterers as static
-- statement:
--   Let $k>0$ be the wavenumber, $v_p\ge0$ the particle speed, $l_s>0$ the scattering mean free path and $c_0>0$ the speed of light, and take the scattering time $\tau=l_s/c_0$ of nonresonant scattering. Then:
--
--   1. $kv_p\tau=\dfrac{v_p}{c_0}\,kl_s$;
--   2. for every threshold $\epsilon>0$, $kv_p\tau\le\epsilon$ if and only if $v_p/c_0\le\epsilon/(kl_s)$;
--   3. if $kl_s>1$, then $\epsilon/(kl_s)<\epsilon$, so the condition is stricter than $v_p/c_0\le\epsilon$;
--   4. the upper limit $\epsilon/(k\tau)$ on $v_p$ strictly decreases as the scattering time $\tau>0$ increases, as it does for resonant scattering.
--
--   **Formalization Note** The paper's "$kv_p\ll1/\tau$" is written $kv_p\tau\le\epsilon$ for an arbitrary threshold $\epsilon>0$, and $\tau\sim l_s/c_0$ is taken as an equality.
-- source:
--   B. X. Wang and C. Y. Zhao, The dependent scattering effect on radiative properties of micro/nanoscale discrete disordered media, arXiv:2003.13288v1 (2020), claim c003; Sec. 3, introductory paragraph, postulation (2), PDF p. 17

import Mathlib
import Definitions.Def_Arxiv2003_13288_Basic

open MeasureTheory Filter Topology

namespace Arxiv2003_13288

theorem static_scatterer_criterion (k vp ls c0 : ℝ) (hk : 0 < k) (hvp : 0 ≤ vp) (hls : 0 < ls)
    (hc0 : 0 < c0) :
    k * vp * (ls / c0) = vp / c0 * (k * ls) ∧
    (∀ ε : ℝ, 0 < ε → (k * vp * (ls / c0) ≤ ε ↔ vp / c0 ≤ ε / (k * ls))) ∧
    (1 < k * ls → ∀ ε : ℝ, 0 < ε → ε / (k * ls) < ε) ∧
    (∀ τ τ' : ℝ, 0 < τ → τ < τ' → ∀ ε : ℝ, 0 < ε → ε / (k * τ') < ε / (k * τ)) := by sorry

end Arxiv2003_13288
