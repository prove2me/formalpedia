-- Prove2me | Theorems.Thm_BartlettNN_FatNet_lemma22_l2_covering_combos
-- name    : BartlettNN.FatNet.lemma22_l2_covering_combos
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:49:23.604734+00:00
-- url     : https://prove2.me/theorems/56992468-360c-46de-8795-ab905e890e2b
-- title:
--   Lemma 22 — log₂ N_2(H, γ, m) ≤ (2M²A²/γ²) log₂(2N_2(F, γ/(2A), m) + 1)
-- statement:
--   Let $F$ be a nonempty class of functions from a set $X$ to $[-M/2,M/2]$, let $A>0$, and let
--
--   $$
--   H=\Big\{\sum_{i=1}^N w_if_i:\ N\in\mathbb N,\ f_i\in F,\ \sum_{i=1}^N|w_i|\le A\Big\}
--   $$
--
--   be the class of Theorem 17. Let $\gamma>0$ and $m\in\mathbb N$. If $\mathcal N_2(F,\gamma/(2A),m)$ is finite, then $\mathcal N_2(H,\gamma,m)$ is finite and
--
--   $$
--   \log_2\mathcal N_2(H,\gamma,m)\ \le\ \frac{2M^2A^2}{\gamma^2}\,\log_2\!\Big(2\,\mathcal N_2\Big(F,\frac{\gamma}{2A},m\Big)+1\Big).
--   $$
--
--   The bound on the network class depends on the output weights only through $A$, and not on the number of hidden units. It is the step of Theorem 17's proof that passes from the hidden layer to the whole network.
--
--   **Formalization Note** $A>0$ and $\gamma>0$ are implicit in the paper's $\gamma/(2A)$ and are stated. The conclusion is stated for every finite value $N$ of $\mathcal N_2(F,\gamma/(2A),m)$: it asserts a finite value $K$ of $\mathcal N_2(H,\gamma,m)$ with $\log_2K\le(2M^2A^2/\gamma^2)\log_2(2N+1)$. Covers are external (they need not lie in $H$), which the paper's proof requires.
-- source:
--   Bartlett, The Sample Complexity of Pattern Classification with Neural Networks, IEEE Trans. Inform. Theory 44 (1998), p. 532, Lemma 22

import Mathlib
import Definitions.Def_BartlettNN_FatNet_coverNum
import Definitions.Def_BartlettNN_FatNet_combos

namespace BartlettNN.FatNet

/-- **Lemma 22** (Bartlett 1998, p. 532).
For the classes of Theorem 17 — `F` a nonempty class of `[−M/2, M/2]`-valued functions on `X`,
`A > 0`, and `H = combos F A` — and `γ > 0`: whenever `N_2(F, γ/(2A), m)` is finite,
`N_2(H, γ, m)` is finite and
`log₂ N_2(H, γ, m) ≤ (2M²A²/γ²) log₂(2 N_2(F, γ/(2A), m) + 1)`.
(`A > 0` and `γ > 0` are implicit in the paper's `γ/(2A)`.) -/
theorem lemma22_l2_covering_combos {X : Type*} (F : Set (X → ℝ)) (M A γ : ℝ) (m : ℕ)
    (hFne : F.Nonempty) (hF : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-M / 2) (M / 2))
    (hA : 0 < A) (hγ : 0 < γ) :
    ∀ N : ℕ, N2 F (γ / (2 * A)) m = N →
      ∃ K : ℕ, N2 (combos F A) γ m = K ∧
        Real.logb 2 K ≤ 2 * M ^ 2 * A ^ 2 / γ ^ 2 * Real.logb 2 (2 * N + 1) := by sorry

end BartlettNN.FatNet
