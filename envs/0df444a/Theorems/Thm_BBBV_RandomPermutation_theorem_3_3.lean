-- Prove2me | Theorems.Thm_BBBV_RandomPermutation_theorem_3_3
-- name    : BBBV.RandomPermutation.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:06:26.931634+00:00
-- url     : https://prove2.me/theorems/b745355f-83a0-416e-8692-6464554581f3
-- title:
--   Theorem 3.3 (corrected) — hybrid bound for modified oracle answers
-- statement:
--   Run a $T$-query unitary algorithm with a baseline oracle answer function $g_0(i,y)$ at each step $i$. Let $F$ be a finite set of step-string pairs and let $g_1$ agree with $g_0$ outside $F$. If $\varepsilon>0$ and the sum of the baseline query magnitudes obeys
--
--   $$\sum_{(i,y)\in F}q_y(\phi_i)\le\frac{\varepsilon^2}{T},$$
--
--   then the two final states differ in norm by at most $2\varepsilon$. Here $\phi_i$ is the baseline state before step $i$.
--
--   This hybrid estimate controls the effect of changing a small collection of query answers.
--
--   **Formalization Note** The baseline may vary by step because the proof of Theorem 3.6 uses a hybrid run. The paper prints $\varepsilon$ as the final bound; the correct bound is $2\varepsilon$. Already for one query with all magnitude on the modified string, changing an XOR answer can move the final state by $2$ while $\varepsilon=1$. At $T=0$ the sum is empty, the two runs coincide, and Lean's $0/0=0$ convention causes no change in meaning.
-- source:
--   Bennett, Bernstein, Brassard and Vazirani, Strengths and weaknesses of quantum computing, arXiv:quant-ph/9701001v1, pp. 7–8, Theorem 3.3 (corrected and generalized for proof of Theorem 3.6)

import Mathlib
import Definitions.Def_BBBV_RandomPermutation_QueryModel

namespace BBBV.RandomPermutation

theorem theorem_3_3 {X R W : Type} [Fintype X] [Fintype R] [Fintype W]
    [AddCommGroup R] {T : ℕ} (M : QueryAlg X R W T)
    (g₀ g₁ : Fin T → X → R) (F : Finset (Fin T × X))
    (hF₀ : ∀ i y, (i, y) ∉ F → g₁ i y = g₀ i y)
    (ε : ℝ) (hε : 0 < ε)
    (hF : (∑ p ∈ F, queryMag p.2 (state M g₀ p.1)) ≤ ε ^ 2 / (T : ℝ)) :
    ‖final M g₀ - final M g₁‖ ≤ 2 * ε := by sorry

end BBBV.RandomPermutation
