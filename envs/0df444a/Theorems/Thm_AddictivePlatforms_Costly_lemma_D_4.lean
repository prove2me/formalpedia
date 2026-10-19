-- Prove2me | Theorems.Thm_AddictivePlatforms_Costly_lemma_D_4
-- name    : AddictivePlatforms.Costly.lemma_D_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T14:38:35.325327+00:00
-- url     : https://prove2.me/theorems/320b4ef2-f530-4203-9533-454e9153fe13
-- title:
--   Lemma D.4, p. 36 — if the equilibrium addictiveness is d¹(κ), the consumer is better off under joint-profit maximization
-- statement:
--   Work under Assumptions 1–3 with $K \ge 2$ platforms, a cap $\overline{A} > 0$ ($\overline{A} = \infty$ allowed) and a cost scale $\kappa > 0$. Let $A(\cdot)$ be the function of Lemma D.1 and let $d^1$ satisfy (A.9) of Lemma D.2. Suppose $(d^E, \sigma^E)$ is a pure-strategy subgame perfect equilibrium in which every platform chooses $d^1$, i.e. the equilibrium addictiveness is $d^1(\kappa)$. Then for every joint-profit maximizing outcome $(d^J, \sigma^J)$,
--   $$U^E \le U^J,$$
--   where $U^E$ and $U^J$ are the consumer's payoffs (1) at the equilibrium and at the joint-profit maximizing outcome.
--
--   When the platforms' marginal trade-off rather than the consumer's participation determines the equilibrium, competition leads to more addictiveness than joint-profit maximization, and the consumer prefers the latter. This is the high-cost half of Proposition 5.
--
--   **Formalization Note.** "Better off" is read weakly ($\le$), which is what the proof establishes. Standing pins as in the model file, plus $K \ge 2$ and $\overline{A} > 0$.
-- source:
--   Ichihashi & Kim, Addictive Platforms, Bank of Canada SWP 2022-16 (Apr. 1, 2022), p. 36, Lemma D.4, and its proof (pp. 36–37, (A.12), (A.13))

import Mathlib
import Definitions.Def_AddictivePlatforms_Costly_Model

open Set Filter Topology
open scoped ENNReal

namespace AddictivePlatforms.Costly

/-- Lemma D.4 (p. 36). Fix `K ≥ 2` platforms, a cap `Ā > 0` (`Ā = ∞` allowed), a cost scale
`κ > 0`, the function `A(·)` of Lemma D.1 (`AD`) and a solution `d¹(κ)` of (A.9) (`d1`). If the
equilibrium addictiveness is `d¹(κ)` — the equilibrium `(d^E, σ^E)` has every platform choose
`d¹(κ)` — then the consumer is (weakly) better off under every joint-profit maximizing outcome
`(d^J, σ^J)` than in that equilibrium. -/
theorem lemma_D_4 (v C γ g : ℝ → ℝ) (K : ℕ) (hK : 2 ≤ K) (hS : Standing v C γ g K)
    (Abar : ℝ≥0∞) (hAbar : 0 < Abar) (κ : ℝ) (hκ : 0 < κ) (AD : ℝ → ℝ) (hAD : IsAD C g K AD)
    (d1 : ℝ) (hd1 : IsD1 AD γ κ Abar K d1)
    (dE : Fin K → ℝ) (σE : AddictivePlatforms.Compete.ConsumerStrategy K) (hE : IsSPE (uOf v) C γ κ Abar dE σE)
    (hdE : ∀ k, dE k = d1)
    (dJ : Fin K → ℝ) (σJ : AddictivePlatforms.Compete.ConsumerStrategy K) (hJ : IsJPM (uOf v) C γ κ Abar dJ σJ) :
    AddictivePlatforms.Compete.consumerSurplus (uOf v) C dE σE ≤ AddictivePlatforms.Compete.consumerSurplus (uOf v) C dJ σJ := by sorry

end AddictivePlatforms.Costly
