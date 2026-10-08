-- Prove2me | Theorems.Thm_AntonelliBFSDE_BackwardForward_lipschitz_estimates
-- name    : AntonelliBFSDE.BackwardForward.lipschitz_estimates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:09:16.000311+00:00
-- url     : https://prove2.me/theorems/3696f3bc-7f36-4283-aed1-b576508965d0
-- title:
--   Proof of Theorem 3.1, p. 787 — pointwise Lipschitz estimates for F and G against dD
-- statement:
--   Under the hypotheses of §3 and the domination of $|dA|$, $|dC|$ by $dD$, let $(U,V), (\tilde U,\tilde V) \in L^1(\mu) \otimes L^1(\mu)$ and write
--   $$\Delta_{s,t}(\omega) = \int_{(s,t]} \big(|U_r - \tilde U_r| + |V_r - \tilde V_r|\big)\,dD_r(\omega) \in [0,\infty].$$
--
--   1. For every $\omega$ and every $t \le T$,
--   $$|F(U,V)_t - F(\tilde U,\tilde V)_t| \le k\,\Delta_{0,t}.$$
--   2. For every càdlàg version $W$ of $G(U,V)$ and $\tilde W$ of $G(\tilde U,\tilde V)$ and every $t \le T$, $\Delta_{t,T}$ is integrable and, $P$-a.s.,
--   $$|W_t - \tilde W_t| \le k\,E\big(\Delta_{t,T} \mid \mathcal F_t\big).$$
--
--   These are the two estimates from which the proof of Theorem 3.1 derives the contraction property: the Lipschitz condition in $(x,y)$, and then $|dA| \le dD$, $|dC| \le dD$.
--
--   **Formalization Note** The step from $|dA|$, $|dC|$ to $dD$ is the paper's "by absolute continuity", which rests on the domination hypothesis `Dominated`. In clause 1 the left side is compared in $[0,\infty]$; in clause 2 $\Delta_{t,T}$ is turned into a real number, and its integrability is part of the conclusion, so the conditional expectation is not the junk value $0$.
-- source:
--   Antonelli, Backward-forward stochastic differential equations, Ann. Appl. Probab. 3(3) (1993), p. 787, proof of Theorem 3.1, the two displays after 'by absolute continuity, we have that'

import Mathlib
import Definitions.Def_AntonelliBFSDE_BackwardForward_Setting
import Definitions.Def_AntonelliBFSDE_BackwardForward_System

open MeasureTheory
open scoped NNReal ENNReal

namespace AntonelliBFSDE.BackwardForward

theorem lipschitz_estimates {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (β : ℝ) (hT : 0 < T)
    (husual : UsualHypotheses 𝓕 P) (IA IC : BVIntegrator 𝓕 T β) (hdom : Dominated IA IC)
    (k : ℝ) (f g : ℝ≥0 → Ω → ℝ → ℝ → ℝ) (Y : Ω → ℝ) (J : ℝ≥0 → Ω → ℝ)
    (hyp : StandingHyp 𝓕 P IA IC k f g Y J)
    (U V U' V' : ℝ≥0 → Ω → ℝ) (hU : MemL1D P IA IC U) (hV : MemL1D P IA IC V)
    (hU' : MemL1D P IA IC U') (hV' : MemL1D P IA IC V') :
    (∀ ω, ∀ t ≤ T, ENNReal.ofReal |Fop IA J f U V t ω - Fop IA J f U' V' t ω| ≤
        ENNReal.ofReal k * pathDist IA IC U V U' V' 0 t ω) ∧
    ∀ W W' : ℝ≥0 → Ω → ℝ, IsGVersion 𝓕 P IC g Y U V W → IsGVersion 𝓕 P IC g Y U' V' W' →
      ∀ t ≤ T, Integrable (fun ω => (pathDist IA IC U V U' V' t T ω).toReal) P ∧
        ∀ᵐ ω ∂P, |W t ω - W' t ω| ≤
          k * (P[fun ω => (pathDist IA IC U V U' V' t T ω).toReal | 𝓕 t]) ω := by sorry

end AntonelliBFSDE.BackwardForward
