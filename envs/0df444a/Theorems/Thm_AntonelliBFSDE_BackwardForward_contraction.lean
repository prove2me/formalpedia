-- Prove2me | Theorems.Thm_AntonelliBFSDE_BackwardForward_contraction
-- name    : AntonelliBFSDE.BackwardForward.contraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:09:28.34001+00:00
-- url     : https://prove2.me/theorems/a52d3c4f-1fca-44da-a5e1-79fb51f4da04
-- title:
--   Proof of Theorem 3.1, p. 788 — ‖Γ(U, V) − Γ(Ũ, Ṽ)‖ ≤ k‖D‖_{H^∞}‖(U, V) − (Ũ, Ṽ)‖
-- statement:
--   Under the hypotheses of §3 and the domination of $|dA|$, $|dC|$ by $dD$, let $(U,V)$ and $(\tilde U,\tilde V)$ be progressively measurable pairs in $L^1(\mu) \otimes L^1(\mu)$, and let $W$, $\tilde W$ be càdlàg versions of $G(U,V)$, $G(\tilde U,\tilde V)$. Then
--   $$\|F(U,V) - F(\tilde U,\tilde V)\|_{L^1(\mu)} + \|W - \tilde W\|_{L^1(\mu)} \le k\,\|D\|_{\mathbf H^\infty}\big(\|U - \tilde U\|_{L^1(\mu)} + \|V - \tilde V\|_{L^1(\mu)}\big),$$
--   that is, $\|\Gamma(U,V) - \Gamma(\tilde U,\tilde V)\|_{L^1\otimes L^1} \le k\|D\|_{\mathbf H^\infty}\|(U,V) - (\tilde U,\tilde V)\|_{L^1\otimes L^1}$, where $\|D\|_{\mathbf H^\infty} = \operatorname{ess\,sup} D_T$.
--
--   When $k\|D\|_{\mathbf H^\infty} < 1$, $\Gamma$ is therefore a contraction, which is the first assertion of Theorem 3.1.
--
--   **Formalization Note** The pairs are progressively measurable because the proof combines the two estimates "by the adaptedness of the processes" (p. 787): $F(U,V)_t - F(\tilde U,\tilde V)_t$ must be $\mathcal F_t$-measurable. All norms are lower integrals in $[0,\infty]$, and the product on the right is computed in $[0,\infty]$.
-- source:
--   Antonelli, Backward-forward stochastic differential equations, Ann. Appl. Probab. 3(3) (1993), p. 788, proof of Theorem 3.1, the display after 'or'

import Mathlib
import Definitions.Def_AntonelliBFSDE_BackwardForward_Setting
import Definitions.Def_AntonelliBFSDE_BackwardForward_System

open MeasureTheory
open scoped NNReal ENNReal

namespace AntonelliBFSDE.BackwardForward

theorem contraction {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (β : ℝ) (hT : 0 < T)
    (husual : UsualHypotheses 𝓕 P) (IA IC : BVIntegrator 𝓕 T β) (hdom : Dominated IA IC)
    (k : ℝ) (f g : ℝ≥0 → Ω → ℝ → ℝ → ℝ) (Y : Ω → ℝ) (J : ℝ≥0 → Ω → ℝ)
    (hyp : StandingHyp 𝓕 P IA IC k f g Y J)
    (U V U' V' : ℝ≥0 → Ω → ℝ)
    (hUp : IsProgressive 𝓕 U) (hVp : IsProgressive 𝓕 V)
    (hU'p : IsProgressive 𝓕 U') (hV'p : IsProgressive 𝓕 V')
    (hU : MemL1D P IA IC U) (hV : MemL1D P IA IC V)
    (hU' : MemL1D P IA IC U') (hV' : MemL1D P IA IC V')
    (W W' : ℝ≥0 → Ω → ℝ) (hW : IsGVersion 𝓕 P IC g Y U V W)
    (hW' : IsGVersion 𝓕 P IC g Y U' V' W') :
    L1NormD P IA IC (Fop IA J f U V - Fop IA J f U' V') + L1NormD P IA IC (W - W') ≤
      ENNReal.ofReal k * HInfNorm P IA IC *
        (L1NormD P IA IC (U - U') + L1NormD P IA IC (V - V')) := by sorry

end AntonelliBFSDE.BackwardForward
