-- Prove2me | Theorems.Thm_DriverSurge_IC_theorem_4
-- name    : DriverSurge.IC.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:31:22.413933+00:00
-- url     : https://prove2.me/theorems/7ab52ba2-a180-416f-9479-c5c61ca1eb1b
-- title:
--   Theorem 4, p. 58 — with i = 2 the surge state, an optimal policy has σ_1 = (0, t_1) / (t_2, t_3) / (0, ∞) and σ_2 = (t_4, ∞) / (0, t_5) ∪ (t_6, ∞) / (0, ∞), and only such policies are optimal
-- statement:
--   Let the trip-length laws have bounded densities and finite means, let the payments $w_1,w_2$ be continuous on $(0,\infty)$ and $F_k$-integrable there, and let state $2$ be the surge state: some policy $\sigma_2$ has $R_2(w_2,\sigma_2)>R_1(w_1,\sigma_1)$ for every policy $\sigma_1$. Then there is a policy $\sigma=\{\sigma_1,\sigma_2\}$ maximizing the reward $R(w,\sigma)$ over all policies, with:
--
--   1. **Non-surge state** $\sigma_1$ (affine prices have $m_1\ge0$):
--      - if $w_1(\tau)=m_1\tau+a_1$ with $a_1\ge0$, then $\sigma_1=(0,t_1)$ for some $t_1\in[0,\infty]$;
--      - if $w_1(\tau)=m_1\tau-a_1$ with $a_1>0$, then $\sigma_1=(t_2,t_3)$ for some $t_2,t_3\in[0,\infty]$;
--      - if $\partial R(w,\sigma')/\partial u>0$ for every policy $\sigma'$ and every upper endpoint $u$ of an interval of $\sigma'_1$, then $\sigma_1=(0,\infty)$;
--   2. **Surge state** $\sigma_2$ (with $m_2\ge0$):
--      - if $w_2(\tau)=m_2\tau-a_2$ with $a_2\ge0$, then $\sigma_2=(t_4,\infty)$ for some $t_4\in[0,\infty)$;
--      - if $w_2(\tau)=m_2\tau+a_2$ with $a_2>0$, then $\sigma_2=(0,t_5)\cup(t_6,\infty)$ for some $t_5,t_6\in[0,\infty]$;
--      - if $\partial R(w,\sigma')/\partial u>0$ for every policy $\sigma'$ and every upper endpoint $u$ of an interval of $\sigma'_2$, then $\sigma_2=(0,\infty)$.
--
--   Furthermore, only policies of the given forms can be optimal: every maximizing policy has $\sigma_1$ and $\sigma_2$ of these forms up to $F_1$- and $F_2$-null sets.
--
--   $$\max_{\sigma}R(w,\sigma)\ \text{is attained, and only at policies of the forms above.}$$
--
--   This subsumes the structural part of Theorem 2 and, through its third bullets, is the step of Theorem 3's proof that turns positivity of the endpoint derivative into optimality of accepting everything.
--
--   **Formalization Note** Lean state `0` is the paper's non-surge state 1 and Lean state `1` the surge state 2; `other i` is the state $j\ne i$. The reward is the closed form $R(w,\sigma)=\mu_1R_1+\mu_2R_2$, which Lemma 1 identifies with the driver's earnings rate.
--
--   Differences from the source:
--   - reading: "$\partial/\partial u R(w,\sigma')>0$" → $r(u,i,w,\sigma')>0$ at every upper endpoint $u$ of an interval of $\sigma'_i$; reason: D.3.1 fixes $\propto$ as "same sign except where $f(u)=0$"; read literally, $\partial R/\partial u>0$ would fail wherever $f_i(u)=0$
--   - reading: the surge bullets print "$\sigma_1=(t_4,\infty)$" and "$\sigma_1=(0,t_5)\cup(t_6,\infty)$" → $\sigma_2$; reason: typo; Theorem 2 (p. 11) states them for $\sigma_2$
--   - reading: $R(w,\sigma)$, the earnings rate → the closed form $\mu_1R_1+\mu_2R_2$; reason: Lemma 1 proves the two equal; the paper's proof works with the closed form
--   - encoding: affine prices $w_i(\tau)=m_i\tau\pm a_i$ → with $m_i\ge0$; reason: §2.4 (p. 8) defines affine pricing with $m_i\ge0$
--   - encoding: D.3.1 standing assumptions and $w_i$ continuous (p. 5) → bounded densities, finite means, $w_k$ continuous on $(0,\infty)$ and $F_k$-integrable there; reason: standing assumptions; finite means and integrability exclude only cases where $T_i$, $W_i$ are undefined
--   - generalization: $w_k$ asymptotically sub-linear (p. 5) → not assumed; reason: the theorem's statement does not involve it; integrability already makes the rates finite
-- source:
--   Garg, Nazerzadeh, Driver Surge Pricing, arXiv:1905.07544v4, p. 58, Theorem 4 (proof pp. 58–60)

import Mathlib
import Definitions.Def_DriverSurge_IC_Pricing

namespace DriverSurge.IC

open MeasureTheory Set

/-- Theorem 4 (p. 58). Let the densities be bounded, the means finite, the payments `w_i` continuous on
`(0, ∞)` and `F_i`-integrable there, and let state 2 (Lean `1`) be the surge state. Then some policy
maximizing `R(w, σ)` over all policies has `σ_1` of the non-surge form and `σ_2` of the surge form
(`NonSurgeForm`, `SurgeForm`: each bullet whose hypothesis on `w` holds fixes the shape), and every
maximizing policy has `σ_1`, `σ_2` of these forms up to `F_1`-, `F_2`-null sets. -/
theorem theorem_4 (P : Primitives) (f : Fin 2 → ℝ → ℝ) (hf : HasBoundedDensity P f)
    (hmean : FiniteMean P) (w : Fin 2 → ℝ → ℝ) (hwc : ∀ k, ContinuousOn (w k) (Ioi 0))
    (hwi : ∀ k, IntegrableOn (w k) (Ioi 0) (P.F k)) (hsurge : IsSurgeState P w) :
    (∃ σ, IsPolicy σ ∧ (∀ σ', IsPolicy σ' → rewardCF P w σ' ≤ rewardCF P w σ) ∧
      NonSurgeForm P w (σ 0) ∧ SurgeForm P w (σ 1)) ∧
    (∀ σ, IsPolicy σ → (∀ σ', IsPolicy σ' → rewardCF P w σ' ≤ rewardCF P w σ) →
      (∃ s, NonSurgeForm P w s ∧ EqUpToNull (P.F 0) (σ 0) s) ∧
      (∃ s, SurgeForm P w s ∧ EqUpToNull (P.F 1) (σ 1) s)) := by sorry

end DriverSurge.IC
