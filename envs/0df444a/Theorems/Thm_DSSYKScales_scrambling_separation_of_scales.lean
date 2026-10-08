-- Prove2me | Theorems.Thm_DSSYKScales_scrambling_separation_of_scales
-- name    : DSSYKScales.scrambling_separation_of_scales
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T01:48:38.063774+00:00
-- url     : https://prove2.me/theorems/023fb7e9-4825-43ce-bba2-0b7b61388d1c
-- title:
--   Separation of scales in DSSYK$_\infty$ scrambling: fast in string units, hyperfast in cosmic units
-- statement:
--   Let $(N_n,q_n)$ be a double-scaled sequence of DSSYK$_\infty$ models with parameter $\lambda>0$ (so $N_n\to\infty$ and $q_n^2/N_n\to\lambda$). Let $\mathcal J>0$. Let $P_{N,q}(t)=1-\bigl(1+\tfrac qN e^{(q-1)\mathcal J t}\bigr)^{-1/(q-1)}$ be the epidemic scrambling probability in cosmic time $t$ (eq. (8.1)). Then both of the following hold.
--
--   1. **Early times, string units** (eq. (8.3)). For every fixed string time $t_s\in\mathbb R$, with cosmic time $t_c=t_s/q_n$,
--   $$\lim_{n\to\infty} N_n\,P_{N_n,q_n}\!\Bigl(\frac{t_s}{q_n}\Bigr)=e^{\mathcal J t_s}.$$
--   2. **Late times, cosmic units** (eq. (8.6)). For every fixed cosmic time $t_c>0$,
--   $$\lim_{n\to\infty}\bigl(1-P_{N_n,q_n}(t_c)\bigr)=e^{-\mathcal J t_c}.$$
--
--   Together these are the paper's scrambling example of the separation of scales. Early scrambling is ordinary fast scrambling in string time $t_s=q\,t_c$ and collapses to an instant in cosmic time. Late scrambling is a quasinormal-mode decay at rate $\mathcal J$ in cosmic time and becomes infinitely slow in string time.
--
--   **Formalization Note** The paper's "$\approx$" and "for small $t_c$" are read as exact limits along the double-scaled sequence at fixed $t_s$ (resp. fixed $t_c>0$).
-- source:
--   L. Susskind, "De Sitter Space, Double-Scaled SYK, and the Separation of Scales in the Semiclassical Limit", arXiv:2209.09999v1 [hep-th] (2022), https://arxiv.org/abs/2209.09999, Section 8 (Scrambling), pp. 32-34, eqs. (8.1), (8.3), (8.6)

import Mathlib
import Definitions.Def_DSSYKScales_defs

open Filter Topology

namespace DSSYKScales
theorem scrambling_separation_of_scales (N q : ℕ → ℕ) (lam J : ℝ) (hJ : 0 < J)
    (hlim : IsDoubleScaledLimit N q lam) :
    (∀ ts : ℝ, Tendsto (fun n => (N n : ℝ) * scramblingProbability (N n) (q n) J (ts / (q n : ℝ)))
      atTop (𝓝 (Real.exp (J * ts)))) ∧
    (∀ tc : ℝ, 0 < tc → Tendsto (fun n => 1 - scramblingProbability (N n) (q n) J tc)
      atTop (𝓝 (Real.exp (-(J * tc))))) := by sorry
end DSSYKScales
