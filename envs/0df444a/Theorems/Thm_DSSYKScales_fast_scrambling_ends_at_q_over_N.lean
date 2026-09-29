-- Prove2me | Theorems.Thm_DSSYKScales_fast_scrambling_ends_at_q_over_N
-- name    : DSSYKScales.fast_scrambling_ends_at_q_over_N
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T01:55:37.42637+00:00
-- url     : https://prove2.me/theorems/a197f2c7-8761-437a-8f07-4f8617b85722
-- title:
--   End of fast scrambling: at $t_s=\log q/\mathcal J$ one has $P\sim q/N$
-- statement:
--   Let $(N_n,q_n)$ be double scaled with parameter $\lambda>0$, let $\mathcal J>0$, and let $P_{N,q}$ be the scrambling probability (8.1). Evaluate $P$ at the end of the fast-scrambling window, i.e. at string time $\Delta t_s=\log q/\mathcal J$ (eq. (8.4)), equivalently cosmic time $\Delta t_c=\log q/(q\mathcal J)$ (eq. (8.5)). Then
--   $$\lim_{n\to\infty}\frac{N_n}{q_n}\,P_{N_n,q_n}\!\Bigl(\frac{\log q_n}{q_n\,\mathcal J}\Bigr)=\frac{\log(1+\lambda)}{\lambda}.$$
--
--   So at the end of the window, $P$ is of order $q/N$, with the explicit constant $\log(1+\lambda)/\lambda\in(0,1)$. This makes precise the paper's statement that fast scrambling "only lasts a short time until $P\sim q/N$", whereas standard fast scrambling lasts until $P\sim1$.
--
--   **Formalization Note** The paper states only the order of magnitude $P\sim q/N$. The limit constant $\log(1+\lambda)/\lambda$ is the exact value implied by (8.1) at time (8.5).
-- source:
--   L. Susskind, "De Sitter Space, Double-Scaled SYK, and the Separation of Scales in the Semiclassical Limit", arXiv:2209.09999v1 [hep-th] (2022), https://arxiv.org/abs/2209.09999, Section 8, p. 33, text after eq. (8.3) and eqs. (8.4)-(8.5)

import Mathlib
import Definitions.Def_DSSYKScales_defs

open Filter Topology

namespace DSSYKScales
theorem fast_scrambling_ends_at_q_over_N (N q : ℕ → ℕ) (lam J : ℝ) (hJ : 0 < J)
    (hlim : IsDoubleScaledLimit N q lam) :
    Tendsto (fun n => (N n : ℝ) / (q n : ℝ) *
        scramblingProbability (N n) (q n) J (Real.log (q n : ℝ) / ((q n : ℝ) * J)))
      atTop (𝓝 (Real.log (1 + lam) / lam)) := by sorry
end DSSYKScales
