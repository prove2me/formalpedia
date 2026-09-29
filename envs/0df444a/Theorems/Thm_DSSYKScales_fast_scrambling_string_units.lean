-- Prove2me | Theorems.Thm_DSSYKScales_fast_scrambling_string_units
-- name    : DSSYKScales.fast_scrambling_string_units
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T01:50:39.67457+00:00
-- url     : https://prove2.me/theorems/b8fb5200-8a89-446e-a746-10e3727af320
-- title:
--   Early-time scrambling in string units: $N P(t_s/q)\to e^{\mathcal J t_s}$
-- statement:
--   Let $(N_n,q_n)$ be double scaled with parameter $\lambda>0$, let $\mathcal J\in\mathbb R$, and let $P_{N,q}$ be the scrambling probability (8.1). Fix a string time $t_s\in\mathbb R$ and use cosmic time $t_c=t_s/q_n$ (the relation $t_s=q\,t_c$). Then
--   $$\lim_{n\to\infty} N_n\,P_{N_n,q_n}\!\Bigl(\frac{t_s}{q_n}\Bigr)=e^{\mathcal J t_s}.$$
--
--   This is eq. (8.3), $P=e^{\mathcal J t_s}/N$. In string units the onset of scrambling is ordinary exponential operator growth with a finite rate. In cosmic units the same growth, (8.2), has the divergent rate $(q-1)\mathcal J$.
-- source:
--   L. Susskind, "De Sitter Space, Double-Scaled SYK, and the Separation of Scales in the Semiclassical Limit", arXiv:2209.09999v1 [hep-th] (2022), https://arxiv.org/abs/2209.09999, Section 8, pp. 32-33, eqs. (8.1)-(8.3)

import Mathlib
import Definitions.Def_DSSYKScales_defs

open Filter Topology

namespace DSSYKScales
theorem fast_scrambling_string_units (N q : ℕ → ℕ) (lam J : ℝ)
    (hlim : IsDoubleScaledLimit N q lam) (ts : ℝ) :
    Tendsto (fun n => (N n : ℝ) * scramblingProbability (N n) (q n) J (ts / (q n : ℝ)))
      atTop (𝓝 (Real.exp (J * ts))) := by sorry
end DSSYKScales
