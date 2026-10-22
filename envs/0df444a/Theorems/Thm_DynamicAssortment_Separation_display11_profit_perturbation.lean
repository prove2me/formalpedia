-- Prove2me | Theorems.Thm_DynamicAssortment_Separation_display11_profit_perturbation
-- name    : DynamicAssortment.Separation.display11_profit_perturbation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T10:11:57.152831+00:00
-- url     : https://prove2.me/theorems/b3a6ac61-d76d-4f3f-8fb7-103a4717f4cb
-- title:
--   Display (11) (p. 402) — |r(S, μ) − r(S, μ̂)| ≤ ‖w‖_∞ K C ‖μ − μ̂‖_S
-- statement:
--   Let $1\le C\le N$, $w_i>0$, and let $f$ be a positive noise density. Suppose that for some constant $K>0$ every choice-probability map $\nu\mapsto(p_i(S,\nu))_i$, $S\in\mathcal S$, is $K$-Lipschitz in the sup norm. Then for every $S\in\mathcal S$ and every mean-utility vector $\nu$,
--   $$|r(S,\mu)-r(S,\nu)|\le\|w\|_\infty\,K\,C\,\|\mu-\nu\|_S,$$
--   where $\|w\|_\infty=\max_i w_i$ and $\|\mu-\nu\|_S=\max_{i\in S}|\mu_i-\nu_i|$.
--
--   It bounds how much the single-sale profit of a fixed assortment can move when the mean utilities are replaced by estimates; in the proof of Theorem 2 it is applied with $\nu=\hat\mu_t$.
--
--   **Formalization Note** The statement is deterministic and holds for every $\nu$, in particular for every realization of $\hat\mu_t$. The page's intermediate display, $\max\{|p_i(S,\mu)-p_i(S,\hat\mu_t)|: i\in S\}\le K\|\mu-\hat\mu_t\|_S$, is part of the proof. The hypothesis on $K$ is item 4 of Assumption 1 (`Identifiability.lipschitz`), stated here directly.
-- source:
--   Sauré, Zeevi, Optimal Dynamic Assortment Planning with Demand Learning, Manuf. Serv. Oper. Manag. 15(3), 2013, p. 402, App. A, proof of Theorem 2, Step 2, display (11)

import Mathlib
import Definitions.Def_DynamicAssortment_Separation_ChoiceModel

namespace DynamicAssortment.Separation

/-- Display (11) (App. A, Step 2, p. 402): if every `p(S, ·)`, `S ∈ 𝒮`, is `K`-Lipschitz, then
`|r(S, μ) - r(S, ν)| ≤ ‖w‖_∞ K C ‖μ - ν‖_S` for every `S ∈ 𝒮` and every `ν`. -/
theorem display11_profit_perturbation {N C : ℕ} (hC : 1 ≤ C) (hCN : C ≤ N)
    (f : ℝ → ℝ) (hf : IsNoiseDensity f) (w : Fin N → ℝ) (hw : ∀ i, 0 < w i)
    (μ : Fin N → ℝ) (K : NNReal) (hK : 0 < K)
    (hlip : ∀ S ∈ assortments N C,
      LipschitzWith K (fun ν : Fin N → ℝ => fun i => choiceProb f ν S i)) :
    ∀ S ∈ assortments N C, ∀ ν : Fin N → ℝ,
      |profit f w μ S - profit f w ν S| ≤ normOn Finset.univ w * K * C * normOn S (μ - ν) := by sorry

end DynamicAssortment.Separation
