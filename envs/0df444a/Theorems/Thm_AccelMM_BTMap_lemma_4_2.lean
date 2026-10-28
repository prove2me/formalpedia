-- Prove2me | Theorems.Thm_AccelMM_BTMap_lemma_4_2
-- name    : AccelMM.BTMap.lemma_4_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T00:34:17.02274+00:00
-- url     : https://prove2.me/theorems/6713a5d0-7d75-4753-9e07-5449dd266244
-- title:
--   Lemma 4.2, p. 13 — the rescaling Π does not decrease ρ and makes ∇ρ orthogonal to 1
-- statement:
--   Let $\alpha>1$ and $\beta>0$, and let $\Pi(w)=w+c(w)\mathbf 1$ be the rescaling (4.4)–(4.5). For all $w\in\mathbb R^n$,
--   $$\rho(\Pi(w))\ge\rho(w)\qquad\text{(4.6)}$$
--   and
--   $$\nabla\rho(\Pi(w))^\top\mathbf 1=0.\qquad\text{(4.7)}$$
--
--   So $\Pi$ satisfies conditions (P1) and (P2) of the framework for $f=-\rho$ and $d=\mathbf 1$: rescaling never hurts, and it moves every iterate to the set on which the PL inequality of (F2) holds.
--
--   **Formalization Note** The page prints no hypotheses; $\alpha>1$ is needed because $c$ takes $\log\frac{(\alpha-1)n}{\beta}$ (the paper's $\alpha\ge1$ allows $\log0$), and $\beta>0$ is the standing assumption on the prior.
-- source:
--   Vojnović, Yun & Zhou, Accelerated MM Algorithms for Ranking Scores Inference from Comparison Data, arXiv:1901.00150v3 (26 Dec 2020), p. 13, Lemma 4.2, (4.6)–(4.7)

import Mathlib
import Definitions.Def_AccelMM_BTMap_Framework
import Definitions.Def_AccelMM_BTMap_Model

namespace AccelMM.BTMap

open scoped InnerProductSpace

theorem lemma_4_2 {n : ℕ} (d : Fin n → Fin n → ℕ) (α β : ℝ) (hα : 1 < α) (hβ : 0 < β) :
    (∀ w : E n, rho α β d (Pi α β w) ≥ rho α β d w) ∧
      (∀ w : E n, ⟪gradient (rho α β d) (Pi α β w), ones n⟫_ℝ = 0) := by sorry

end AccelMM.BTMap
