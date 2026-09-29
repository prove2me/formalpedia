-- Prove2me | Theorems.Thm_AKSSorting_Core_expander_exists
-- name    : AKSSorting.Core.expander_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T10:01:08.296565+00:00
-- url     : https://prove2.me/theorems/b27468c9-9fa9-496c-bc16-f428006347a1
-- title:
--   Lemma 3 — bounded-degree ⟨k, ε⟩ bipartite expanders exist
-- statement:
--   For all real $0<\varepsilon<1$ and $c\ge 1$ there is a positive integer $k=k(\varepsilon,c)$ such that for all disjoint finite sets $A$, $B$ with
--   $$ \frac1c\le\frac{|A|}{|B|}\le c $$
--   there is a $\langle k,\varepsilon\rangle$ expander on $\langle A,B\rangle$.
--
--   The degree bound $k$ depends only on $\varepsilon$ and $c$, not on the sizes of $A$ and $B$. This is what keeps every parallel step of the AKS network of constant depth. The paper derives it from the results of Margulis and of Gabber and Galil.
--
--   **Formalization Note** The constant $k$ is quantified before the vertex type and the sets. The ratio condition is written as $|A|\le c|B|$ and $|B|\le c|A|$; for nonempty sets this is the paper's condition, and it additionally admits $A=B=\emptyset$, where the empty graph is an expander. The expander notion is the one of Definition 2.2 with the expansion inequalities imposed on nonempty sets (as printed they fail for the empty set).
-- source:
--   Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983), p. 6, Lemma 3

import Mathlib
import Definitions.Def_AKSSorting_Core_IsExpander

namespace AKSSorting.Core

/-- Lemma 3 (Ajtai–Komlós–Szemerédi 1983, p. 6): for all `0 < ε < 1` and `c ≥ 1` there is a
positive integer `k = k(ε, c)` such that for all disjoint finite sets `A, B` with
`1/c ≤ |A|/|B| ≤ c` there is a `⟨k, ε⟩` expander on `⟨A, B⟩`. The ratio condition is written
multiplicatively, `|A| ≤ c|B|` and `|B| ≤ c|A|`. -/
theorem expander_exists (ε c : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1) (hc : 1 ≤ c) :
    ∃ k : ℕ, 0 < k ∧ ∀ (V : Type) (A B : Finset V), Disjoint A B →
      (A.card : ℝ) ≤ c * B.card → (B.card : ℝ) ≤ c * A.card →
      ∃ G : SimpleGraph V, IsExpander G A B k ε := by sorry

end AKSSorting.Core
