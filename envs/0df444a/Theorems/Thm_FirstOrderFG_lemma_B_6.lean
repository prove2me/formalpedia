-- Prove2me | Theorems.Thm_FirstOrderFG_lemma_B_6
-- name    : FirstOrderFG.lemma_B_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:01:42.390124+00:00
-- url     : https://prove2.me/theorems/2b5fe6cf-c206-4e18-8db7-76ad74484064
-- title:
--   Lemma B.6 — the regret of an epoch of Algorithm 4 is $O(\ln(MT)/\theta_{m,\lambda})$
-- statement:
--   Throughout, $G=(V,E)$ is a strongly observable directed graph on $K\ge2$ arms ($i\to j$: playing $i$ reveals the loss of $j$), $T\ge3$ is the horizon, and the oblivious adversary fixes losses $\ell_1,\dots,\ell_T\in[0,1]^K$ in advance.
--
--   There is a universal constant $C>0$ with the following property. Let $(m,\lambda)$ be an epoch of Algorithm 4 with rounds $\mathcal T_{m,\lambda}$, first round $t^{\mathrm{start}}_{m,\lambda}$ and master rate $\theta_{m,\lambda}$, and let
--   $$
--   \mathrm{Reg}_{m,\lambda,k}=\mathbb E_{t^{\mathrm{start}}_{m,\lambda}}\Big[\sum_{t\in\mathcal T_{m,\lambda}}\big(\langle x_t,g_t\rangle-\ell_{t,k}\big)\Big]
--   $$
--   be its expected regret against $k$ conditional on the history before $t^{\mathrm{start}}_{m,\lambda}$. Then for every $k\in V$,
--   $$
--   \mathrm{Reg}_{m,\lambda,k}\le C\,\frac{\ln(MT)}{\theta_{m,\lambda}} .
--   $$
--
--   Summing this bound over the epochs yields Theorem 4.3.
--
--   **Formalization Note** An epoch is identified by a history $h_0$ of rounds $1,\dots,t_0-1$ after which the instance playing round $t_0$ (after lines 4–9 of Algorithm 4) has played no earlier round.
--
--   Differences from the source:
--   - encoding: $O(\ln(MT)/\theta_{m,\lambda})$ → $\exists C>0$ (before all other quantifiers) with $\le C\ln(MT)/\theta_{m,\lambda}$; reason: $O(\cdot)$ hides universal constants (p.3)
--   - encoding: every epoch $(m,\lambda)$ → every epoch with at least one round, identified by the history before its first round; reason: an epoch without rounds has $\mathrm{Reg}_{m,\lambda,k}=0$ (empty sum) and the bound holds trivially
--   - encoding: conditional expectation $\mathbb E_{t^{\mathrm{start}}}$ → finite sum over the continuations of the history (trajectory law); reason: every history has positive probability (all $\pi_t$ are interior); same values
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Lemma B.6, Eq. (90), p.33

import Mathlib
import Definitions.Def_FirstOrderFG_StronglyObservable
import Definitions.Def_FirstOrderFG_InteriorStart
import Definitions.Def_FirstOrderFG_Alg4_epochReg
import Definitions.Def_FirstOrderFG_Alg4_prepare
import Definitions.Def_FirstOrderFG_Alg4_run
import Definitions.Def_FirstOrderFG_Bset

namespace FirstOrderFG

/-- **Lemma B.6: the regret of one epoch of Algorithm 4.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Lemma B.6, p.33: "For an epoch
`(m, λ)` of Algorithm 4, denote by `T_{m,λ}` its rounds, by `t^start_{m,λ}` and `t^end_{m,λ}` its first and
last rounds, and by `Reg_{m,λ,k} ≜ E_{t^start}[∑_{t ∈ T_{m,λ}} (⟨x_t, g_t⟩ − ℓ_{t,k})]` its expected
regret conditional on the history before `t^start_{m,λ}`. Then, for every `k ∈ V`,
`Reg_{m,λ,k} ≤ O(ln(MT)/θ_{m,λ})`. (90)"

There is a universal constant `C` such that for every instance of the problem, every history `h0`
of rounds `1, …, t₀ − 1` (`t₀ ≤ T`) after which an epoch starts at round `t₀` (the instance playing
round `t₀`, after lines 4–9, has played no earlier round), and every arm `k`,
`Reg_{m,λ,k} ≤ C ln(MT)/θ_{m,λ}`.

**Formalization Note.** `O(·)` hides a universal constant (p.3), so `∃ C` precedes all other
binders. Epochs that have no round are not covered (their regret is `0`). `θ_{m,λ}` is the input `θ`
of the epoch's instance; `M = |B|`, `ln = Real.log`. -/
theorem lemma_B_6 :
    ∃ C : ℝ, 0 < C ∧ ∀ (K T : ℕ), 2 ≤ K → 3 ≤ T →
      ∀ (E : Fin K → Fin K → Prop) [DecidableRel E], StronglyObservable E →
      ∀ ℓ : ℕ → Fin K → ℝ, (∀ t ∈ Finset.Icc 1 T, ∀ i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) →
      ∀ q₀ : (Fin K → ℝ) → ℝ → Fin K → ℝ, InteriorStart E q₀ →
      ∀ h0 : List (Fin K), h0.length < T →
      (Alg4.prepare E T q₀ (Alg4.run E T ℓ q₀ h0)).inst.n = 0 →
      ∀ k : Fin K, Alg4.epochReg E T ℓ q₀ h0 k
        ≤ C * Real.log (((Bset E).card : ℝ) * T)
          / (Alg4.prepare E T q₀ (Alg4.run E T ℓ q₀ h0)).inst.θ := by sorry

end FirstOrderFG
