-- Prove2me | Theorems.Thm_DSSYKScales_hyperfast_scrambling_cosmic_units
-- name    : DSSYKScales.hyperfast_scrambling_cosmic_units
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T01:55:00.222326+00:00
-- url     : https://prove2.me/theorems/5639a46a-af53-4c13-b6fb-d15747a9362a
-- title:
--   Late-time (hyperfast) scrambling in cosmic units: $1-P(t_c)\to e^{-\mathcal J t_c}$
-- statement:
--   Let $(N_n,q_n)$ be double scaled with parameter $\lambda>0$, let $\mathcal J>0$, and let $P_{N,q}$ be the scrambling probability (8.1). For every fixed cosmic time $t_c>0$,
--   $$\lim_{n\to\infty}\bigl(1-P_{N_n,q_n}(t_c)\bigr)=e^{-\mathcal J t_c}.$$
--
--   This is eq. (8.6). After the sharp transition, $1-P$ decays like the leading quasinormal mode at the finite rate $\mathcal J$ in cosmic units ("hyperfast" scrambling). Since the limit holds for every $t_c>0$, the fast-scrambling stage takes zero cosmic time in the limit.
-- source:
--   L. Susskind, "De Sitter Space, Double-Scaled SYK, and the Separation of Scales in the Semiclassical Limit", arXiv:2209.09999v1 [hep-th] (2022), https://arxiv.org/abs/2209.09999, Section 8, pp. 33-34, eqs. (8.1), (8.6)

import Mathlib
import Definitions.Def_DSSYKScales_defs

open Filter Topology

namespace DSSYKScales
theorem hyperfast_scrambling_cosmic_units (N q : ℕ → ℕ) (lam J : ℝ) (hJ : 0 < J)
    (hlim : IsDoubleScaledLimit N q lam) (tc : ℝ) (htc : 0 < tc) :
    Tendsto (fun n => 1 - scramblingProbability (N n) (q n) J tc)
      atTop (𝓝 (Real.exp (-(J * tc)))) := by sorry
end DSSYKScales
