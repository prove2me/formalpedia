-- Prove2me | Theorems.Thm_ApproachRegret_ToOLO_lemma15_oracle
-- name    : ApproachRegret.ToOLO.lemma15_oracle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:22:38.477599+00:00
-- url     : https://prove2.me/theorems/01b91b5b-002d-4a84-b24f-e970b504d9b2
-- title:
--   Lemma 15 — a valid halfspace oracle for Algorithm 1
-- statement:
--   Let $K\subseteq\mathbb R^d$ be nonempty, compact, and convex, with $\kappa=\max_{x\in K}\|x\|>0$, and let $u$ and $S$ be the payoff and target of Algorithm 1. There is an oracle $O$ such that, for every halfspace $H=\{z:\langle a,z\rangle\le c\}$ containing $S$, it returns $O(a,c)\in K$ and
--
--   $$\langle a,u(O(a,c),f)\rangle\le c\qquad\text{for every }f\in B_2(1).$$
--
--   This gives the reduction a valid oracle for every eligible halfspace.
--
--   **Formalization Note** The representation includes zero normals and arbitrary offsets; $\kappa>0$ makes the payoff's division meaningful.
-- source:
--   Abernethy, Bartlett, Hazan, Blackwell Approachability and No-Regret Learning are Equivalent, COLT 2011, JMLR W&CP 19, https://proceedings.mlr.press/v19/abernethy11b.html, Lemma 15, p. 37 (PDF p. 11); halfspace oracle definition, p. 32 (PDF p. 6)

import Mathlib
import Definitions.Def_ApproachRegret_ToOLO_AlgorithmOne

open scoped RealInnerProductSpace

namespace ApproachRegret.ToOLO

/-- Lemma 15, p. 37: an oracle for every halfspace containing the target. -/
theorem lemma15_oracle {d : ℕ} (K : Set (E d))
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (hk : 0 < kappa K) :
    ∃ O : E (d + 1) → ℝ → E d,
      ∀ (a : E (d + 1)) (c : ℝ),
        target K ⊆ {z | ⟪a, z⟫ ≤ c} →
        O a c ∈ K ∧
          ∀ f ∈ Metric.closedBall (0 : E d) 1,
            ⟪a, payoff K (O a c) f⟫ ≤ c := by sorry

end ApproachRegret.ToOLO
