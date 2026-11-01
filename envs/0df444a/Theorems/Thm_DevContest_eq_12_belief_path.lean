-- Prove2me | Theorems.Thm_DevContest_eq_12_belief_path
-- name    : DevContest.eq_12_belief_path
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:50:26.557141+00:00
-- url     : https://prove2.me/theorems/03946f80-3563-42c4-bce9-ba39e6d8af98
-- title:
--   Displays (10)–(12), p.ec18 — $p_t$ and $\phi^*_t$ rise strictly to $\bar p$ and $1$ (corrected: $\bar t=+\infty$)
-- statement:
--   Let $\lambda,c>0$ and $2c/\lambda<\bar R<3c/\lambda$. Then:
--
--   1. $0\le\underline p<\bar p<1$;
--   2. $\phi^*_t\in[0,1)$ at every date $t\ge0$, and $\phi^*_t=0$ for $t<\underline t$;
--   3. $p_t$ and $\phi^*_t$ are strictly increasing on $[\underline t,\infty)$;
--   4. $p_t<\bar p$ at every date $t\ge0$;
--   5. $p_t\to\bar p$ and $\phi^*_t\to1$ as $t\to\infty$.
--
--   These are the facts about the disclosure schedule that the equilibrium and the optimality argument use.
--
--   **Formalization Note** Only dates $t\ge0$ occur in the model.
--
--   Differences from the source:
--   - correction: a finite date $\bar t$ with $p_{\bar t}=\bar p$, and $\phi^*_t=1$ for $t\ge\bar t$ → $\bar t=+\infty$: $p_t<\bar p$ and $\phi^*_t<1$ at every date, with $p_t\to\bar p$ and $\phi^*_t\to1$; reason: (12) reads $\dot p=2\lambda(1-p)(\bar p-p)$, so a solution equal to $\bar p$ at a finite date is constant; with $c=\lambda=1$, $\bar R=2.4$ this contradicts $p_{1/6}=1/7$
-- source:
--   Khorasani, Körpeoğlu, Krishnan, Dynamic Development Contests, author manuscript, Theorem 2, displays (10)–(12), p.22; p.ec18

import Mathlib
import Definitions.Def_DevContest_pcsdBelief

open Filter Topology

namespace DevContest

/-- The belief path of PCSD, Khorasani, Körpeoğlu, Krishnan, *Dynamic Development Contests*, author
manuscript, displays (10)–(12), p.22, and p.ec18: `0 ≤ p̲ < p̄ < 1`; `φ*_t ∈ [0,1)` at every date;
`p_t` and `φ*_t` are strictly increasing from `t̲` on; `p_t` stays below `p̄`, and `p_t → p̄`,
`φ*_t → 1`.

**Formalization Note.** Correction of the printed proof line: since `t̄ = +∞`, the path never reaches
`p̄`, and the printed phase "From `t ≥ t̄`, `φ_t = 1`" has no instance. Only `t ≥ 0` is meaningful. -/
theorem eq_12_belief_path {lam c Rbar : ℝ} (hlam : 0 < lam) (hc : 0 < c)
    (hlow : 2 * c / lam < Rbar) (hhigh : Rbar < 3 * c / lam) :
    0 ≤ pLow lam c Rbar ∧ pLow lam c Rbar < pBar lam c Rbar ∧ pBar lam c Rbar < 1 ∧
    (∀ t, 0 ≤ t → phiStar lam c Rbar t ∈ Set.Ico (0 : ℝ) 1) ∧
    (∀ t, 0 ≤ t → t < tLow lam c Rbar → phiStar lam c Rbar t = 0) ∧
    StrictMonoOn (pcsdBelief lam c Rbar) (Set.Ici (tLow lam c Rbar)) ∧
    StrictMonoOn (phiStar lam c Rbar) (Set.Ici (tLow lam c Rbar)) ∧
    (∀ t, 0 ≤ t → pcsdBelief lam c Rbar t < pBar lam c Rbar) ∧
    Tendsto (pcsdBelief lam c Rbar) atTop (𝓝 (pBar lam c Rbar)) ∧
    Tendsto (phiStar lam c Rbar) atTop (𝓝 1) := by sorry

end DevContest
