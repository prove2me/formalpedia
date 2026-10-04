-- Prove2me | Theorems.Thm_EkelandVP_Constraints_ekeland_point_feasible
-- name    : EkelandVP.Constraints.ekeland_point_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:51:34.355686+00:00
-- url     : https://prove2.me/theorems/ee72f2e6-2e7f-49bc-807a-3824115d0c6d
-- title:
--   §3, (3.9)–(3.12), pp. 330–331 — a feasible ε²-minimizer v with F(w) ≥ F(v) − ε‖w − v‖ on 𝒞
-- statement:
--   Let $V$ be a real Banach space, $F:V\to\mathbb R$ Fréchet-differentiable and $G_1,\dots,G_m:V\to\mathbb R$ continuously Fréchet-differentiable, with feasible set $\mathcal C$ as in (3.2). Assume $\mathcal C\neq\emptyset$ and that $F$ is bounded below on $\mathcal C$. Then for every $\varepsilon>0$ there is a point $v\in\mathcal C$ such that
--   $$F(v)\le \inf_{w\in\mathcal C}F(w)+\varepsilon^2 \qquad\text{and}\qquad F(w)\ge F(v)-\varepsilon\|w-v\|\quad\text{for all } w\in\mathcal C.$$
--
--   This is the first step of the proof of Theorem 3.1: Ekeland's variational principle (Theorem 1.1) applied to the function equal to $F$ on $\mathcal C$ and $+\infty$ off $\mathcal C$, with $\varepsilon^2$ in place of $\varepsilon$ and $\lambda=\varepsilon$. No regularity of the constraints is needed.
--
--   **Formalization Note.** The infimum is not formed in Lean: the first conclusion is written as $F(v)\le F(w)+\varepsilon^2$ for every $w\in\mathcal C$. Non-emptiness of $\mathcal C$ is an added hypothesis (without it no feasible $v$ exists, and the page's application of Theorem 1.1 needs $\bar F\not\equiv+\infty$). The page prints $\|u-v\|$ and $F(v)$ in (3.12) for $\|w-v_\varepsilon\|$ and $F(v_\varepsilon)$; the Lean states the corrected form. Constraints are indexed by `Fin m` as in the definition of the feasible set.
-- source:
--   Ekeland, On the Variational Principle, J. Math. Anal. Appl. 47 (1974), pp. 330–331, §3, proof of Theorem 3.1, (3.8)–(3.12)

import Mathlib
import Definitions.Def_EkelandVP_Constraints_feasibleSet

namespace EkelandVP.Constraints

/-- Ekeland (1974), §3, proof of Theorem 3.1, (3.8)–(3.12), pp. 330–331: Theorem 1.1 applied to
`F̄ = F` on `𝒞`, `+∞` off `𝒞`, with `ε²` and `λ = ε`, gives a feasible `ε²`-minimizer `v` of `F` on
`𝒞` with `F(w) ≥ F(v) - ε ‖w - v‖` for every feasible `w`. -/
theorem ekeland_point_feasible {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] {m : ℕ} (p : ℕ) (F : V → ℝ) (G : Fin m → V → ℝ)
    (hF : Differentiable ℝ F) (hG : ∀ i, ContDiff ℝ 1 (G i))
    (hne : (feasibleSet p G).Nonempty) (hbdd : BddBelow (F '' feasibleSet p G))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ v ∈ feasibleSet p G,
      (∀ w ∈ feasibleSet p G, F v ≤ F w + ε ^ 2) ∧
      ∀ w ∈ feasibleSet p G, F v - ε * ‖w - v‖ ≤ F w := by sorry

end EkelandVP.Constraints
