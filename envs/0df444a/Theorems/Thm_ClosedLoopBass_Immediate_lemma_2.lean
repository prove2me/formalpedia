-- Prove2me | Theorems.Thm_ClosedLoopBass_Immediate_lemma_2
-- name    : ClosedLoopBass.Immediate.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:24:17.650204+00:00
-- url     : https://prove2.me/theorems/59c5b7fb-74fd-4a3b-9366-f3ed3c696e42
-- title:
--   Lemma 2, p. 7 — rejecting demand first in period tₚ leaves D̂ₜ = D̃ₜ up to tₚ + 1, then D̂ₜ < D̃ₜ; and D⁻_T ≥ D⁺_T
-- statement:
--   Consider the closed-loop sales-planning model under its standing assumptions. Let $(\widehat n,\widehat r)$ be a feasible **partial-fulfillment plan**, whose earliest rejection of demand occurs in period $t_p$ with $1\le t_p<T$. That is, its sales satisfy
--
--   $$
--   \widehat s_t=\widetilde d_t\ \ (1\le t<t_p),\qquad \widehat s_{t_p}<\widetilde d_{t_p},
--   $$
--
--   where $\widetilde d_t$ is the demand of the original Bass process. Let $\widehat D_t$ and $\widehat d_t$ be the plan's cumulative and per-period diffusion demand, and let $\widetilde D_t$ be the Bass trajectory. Then:
--
--   1. $\widehat D_t=\widetilde D_t$ for $1\le t\le t_p+1$;
--   2. $\widehat D_t<\widetilde D_t$ for $t_p+1<t\le T+1$;
--   3. the positive and negative demand differences satisfy
--   $$
--   D_T^-=\sum_{t\le T:\ \widetilde d_t>\widehat d_t}(\widetilde d_t-\widehat d_t)\ \ge\ \sum_{t\le T:\ \widehat d_t>\widetilde d_t}(\widehat d_t-\widetilde d_t)=D_T^+ .
--   $$
--
--   The lemma says that the overall diffusion rate is highest when all demand is immediately met. Rejecting demand slows diffusion permanently from the period after the rejection on. Any demand later regained is no larger than the demand lost.
--
--   **Formalization Note**
--
--   1. "Otherwise" in the paper's first sentence is read as $t_p+1<t\le T+1$. Beyond $T+1$, $\widehat D_t$ depends on the plan's values outside the horizon, which are unconstrained.
--   2. The strict inequality uses the standing assumption $q>0$; with $q=0$, diffusion ignores sales.
--   3. The sums defining $D_T^\pm$ range over the periods $t=1,\dots,T$.
-- source:
--   Nadar, Kaya and Güler, New-Product Diffusion in Closed-Loop Supply Chains, MSOM (Articles in Advance, 2020), doi:10.1287/msom.2019.0864, p. 7, Lemma 2 (with class (b), tp and D−T, D+T defined on p. 7, §4.1)

import Mathlib
import Definitions.Def_ClosedLoopBass_Immediate_Model

namespace ClosedLoopBass.Immediate

/-- Lemma 2, p. 7. Let `(n, r)` be a feasible partial-fulfillment plan whose earliest rejection
period is `t_p < T`: its sales equal the Bass demand `d̃_t` for `t < t_p` and fall short of it at
`t_p`. Then `D_t = D̃_t` for `1 ≤ t ≤ t_p + 1`, `D_t < D̃_t` for `t_p + 1 < t ≤ T + 1`, and
`D⁻_T ≥ D⁺_T`. -/
theorem lemma_2 (P : Params) (hP : Standing P) (n r : ℕ → ℝ) (hfeas : Feasible P n r)
    (tp : ℕ) (htp1 : 1 ≤ tp) (htpT : tp < P.T)
    (hbefore : ∀ t ∈ Finset.Ico 1 tp, sales n r t = dB P t)
    (hreject : sales n r tp < dB P tp) :
    (∀ t : ℕ, 1 ≤ t → t ≤ tp + 1 → D P n r t = DB P t) ∧
    (∀ t : ℕ, tp + 1 < t → t ≤ P.T + 1 → D P n r t < DB P t) ∧
    Dplus P n r ≤ Dminus P n r := by sorry

end ClosedLoopBass.Immediate
