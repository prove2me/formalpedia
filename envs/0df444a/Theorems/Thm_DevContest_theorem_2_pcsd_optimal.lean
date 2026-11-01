-- Prove2me | Theorems.Thm_DevContest_theorem_2_pcsd_optimal
-- name    : DevContest.theorem_2_pcsd_optimal
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:54:11.667476+00:00
-- url     : https://prove2.me/theorems/28de25e7-769c-470b-bc40-21ed9d3326b6
-- title:
--   Theorem 2 — PCSD minimizes the expected lead time of a budget-constrained contest (corrected: $\bar t=+\infty$)
-- statement:
--   Let $\lambda,c>0$ and $2c/\lambda<\bar R<3c/\lambda$. Consider PCSD: the principal discloses nothing before $\underline t$, and from then on discloses a first success arriving at $t$ with probability $\phi^*_t$. Then:
--
--   1. **(Equilibrium)** under PCSD, an agent with no success exerts full effort until she obtains her first success, or her opponent obtains her second success, or the principal discloses the opponent's partial progress, and an agent with one success exerts full effort until the end, and this is a Nash equilibrium;
--   2. **(The path)** $p_{\underline t}=\underline p$, for $t>\underline t$
--   $$
--   \dot p_t=\lambda(1-p_t)^2(1-\phi^*_t)=\lambda(1-p_t)\Bigl(4-2p_t-\frac{4c/\lambda}{\bar R-c/\lambda}\Bigr),
--   $$
--   $p_t\to\bar p$ as $t\to\infty$, and $p$ is the unique solution of this initial value problem on $[\underline t,\infty)$;
--   3. **(Optimality)** for every disclosure policy $D$ and every Nash equilibrium $\sigma$ of the contest under $D$,
--   $$
--   \mathbb E[T]\text{ under PCSD and these strategies}\ \le\ \mathbb E[T]\text{ under }D,\sigma .
--   $$
--
--   This says that the probabilistic change-of-state disclosure policy is an optimal information design for a budget-constrained principal, at the fixed reward $\bar R$.
--
--   **Formalization Note** The policies compete in the fullest class: random, private and asymmetric signals, and all Nash equilibria, symmetric or not. PCSD is evaluated at the stated strategies; agents are indifferent in phase 2, so no claim is made about its other equilibria.
--
--   Differences from the source:
--   - correction: a finite date $\bar t$ with $p_{\bar t}=\bar p$, and $\phi^*_t=1$ for $t\ge\bar t$ → $\bar t=+\infty$: $p_t<\bar p$ and $\phi^*_t<1$ at every date, with $p_t\to\bar p$ and $\phi^*_t\to1$; reason: (12) reads $\dot p=2\lambda(1-p)(\bar p-p)$, so a solution equal to $\bar p$ at a finite date is constant; with $c=\lambda=1$, $\bar R=2.4$ this contradicts $p_{1/6}=1/7$
--   - reading: minimizes the expected lead-time of the contest → the value at the stated strategies is at most the value of every Nash equilibrium of every policy, including random, private and asymmetric ones; reason: p.8 imposes no restriction on the policy, and the fixed reward of p.17 is held; this is the strongest reading
--   - reading: the lead time $\mathbb E[T\cdot1\{i\text{ or }-i\text{ wins at }T\}]$ of (2) → $\mathbb E[T]$ in $[0,\infty]$, which is $\infty$ when the contest may never end; reason: the two agree for contests that end; read literally, the formula would make a contest in which nobody works optimal
--   - reading: the principal informs agents of any change in the state of partial progress → only the first success is disclosed; reason: the theorem and p.21 tie disclosure to the arrival of the first success; from a later success on both agents work anyway
--   - encoding: a stage succeeds at a Poisson arrival with instantaneous probability $\lambda x$ → a stage ends when $\int\lambda x$ reaches an independent unit-exponential clock; reason: this is the standard time change of the same point process; it has the same law for every effort path
-- source:
--   Khorasani, Körpeoğlu, Krishnan, Dynamic Development Contests, author manuscript, Theorem 2, p.22; proof, pp.ec17–ec20

import Mathlib
import Definitions.Def_DevContest_IsNash
import Definitions.Def_DevContest_pcsd

open Filter Topology

namespace DevContest

/-- Theorem 2, Khorasani, Körpeoğlu, Krishnan, *Dynamic Development Contests*, author manuscript,
p.22, corrected: `t̄ = +∞`. Let `2c/λ < R̄ < 3c/λ`. Then:

1. (Equilibrium) the strategies `pcsdEffort` are a Nash equilibrium under PCSD;
2. (Phases 1–2) the belief path starts from `p_t̲ = p̲`, satisfies display (12) after `t̲`, tends to
   `p̄`, and is the unique solution of (12) with that initial value;
3. PCSD minimizes the expected lead time: its value at these strategies is at most the expected lead
   time of every Nash equilibrium of every disclosure policy, which may be random, private and
   asymmetric.

**Formalization Note.** The silent phase and the disclosure rule (10)–(11) are the definitions of
`pcsd` and `phiStar`. The printed boundary condition `p_t̄ = p̄` at a finite `t̄` is impossible: `p̄`
is a rest point of (12), so a solution equal to `p̄` at a finite date is constant, and with
`c = λ = 1`, `R̄ = 2.4` it would contradict `p_{1/6} = 1/7`. The expected lead time is in `[0,∞]`.
PCSD is evaluated at the stated strategies only. -/
theorem theorem_2_pcsd_optimal {lam c Rbar : ℝ} (hlam : 0 < lam) (hc : 0 < c)
    (hlow : 2 * c / lam < Rbar) (hhigh : Rbar < 3 * c / lam) :
    IsNash lam c Rbar (pcsd lam c Rbar) (pcsdEffort lam c Rbar) ∧
    (pcsdBelief lam c Rbar (tLow lam c Rbar) = pLow lam c Rbar ∧
      (∀ t, tLow lam c Rbar < t →
        HasDerivAt (pcsdBelief lam c Rbar)
          (lam * (1 - pcsdBelief lam c Rbar t) ^ 2 * (1 - phiStar lam c Rbar t)) t ∧
        lam * (1 - pcsdBelief lam c Rbar t) ^ 2 * (1 - phiStar lam c Rbar t) =
          lam * (1 - pcsdBelief lam c Rbar t) *
            (4 - 2 * pcsdBelief lam c Rbar t - (4 * c / lam) / (Rbar - c / lam))) ∧
      Tendsto (pcsdBelief lam c Rbar) atTop (𝓝 (pBar lam c Rbar)) ∧
      ∀ q : ℝ → ℝ, ContinuousOn q (Set.Ici (tLow lam c Rbar)) →
        q (tLow lam c Rbar) = pLow lam c Rbar →
        (∀ t, tLow lam c Rbar < t →
          HasDerivAt q (lam * (1 - q t) * (4 - 2 * q t - (4 * c / lam) / (Rbar - c / lam))) t) →
        ∀ t, tLow lam c Rbar ≤ t → q t = pcsdBelief lam c Rbar t) ∧
    ∀ (U M : Type) [MeasurableSpace U] (D : Policy U M) (x : Fin 2 → Strategy U),
      IsNash lam c Rbar D x →
        leadTime lam (pcsd lam c Rbar) (pcsdEffort lam c Rbar) ≤ leadTime lam D x := by sorry

end DevContest
