-- Prove2me | Theorems.Thm_ApproxMWM_Scaling_eligible_weight_and_matched_tightness
-- name    : ApproxMWM.Scaling.eligible_weight_and_matched_tightness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:09:46.745218+00:00
-- url     : https://prove2.me/theorems/abfdc5ee-f372-4b78-bd13-9e06b9a4a2d0
-- title:
--   Lemma 3.6 — eligible edges are heavy, and matched edges are $(1+4\epsilon')$-tight
-- statement:
--   Let $G$ be a finite simple graph with integer edge weights $1\le w(e)\le N=2^L$ and $\epsilon'=2^{-g}\le1/4$, and run the scaling algorithm of Figure 2 with the eligibility of Definition 3.2. Let $i\le L$ be a scale index.
--
--   1. If $i<L$, every edge that is eligible at a time the algorithm searches $G_{\mathrm{elig}}$ in some scale $j\le i$ has weight
--   $$w(e)\ \ge\ N/2^{i+1}+\delta_i .$$
--   2. At every scale $i$, every matched edge $e$ satisfies
--   $$yz(e)\ \le\ (1+4\epsilon')\,w(e).$$
--
--   Part 1 is what allows the linear-time variant to ignore light edges in early scales; part 2 is the approximate tightness fed to Lemma 2.3.
--
--   **Formalization Note** The page says "eligible at any time in scales 0 through $i$". The paper's proof bounds eligible edges during the searches for augmenting paths and blossoms, and the statement is formalized at exactly those moments: the start of an iteration (the Augmentation search) and after augmentation (the Blossom Shrinking search). After the last Dual Adjustment of scale $i$ an unmatched edge between two free vertices with $w_i(e)=N/2^{i+1}$ may be eligible without ever being searched, so the literal "any time" reading would include states the proof does not cover. Part 2 is stated at every state reachable at scale $i$ (start of scale or between iterations).
-- source:
--   Duan and Pettie, Linear-Time Approximation for Maximum Weight Matching, J. ACM 61(1), Article 1 (2014), https://doi.org/10.1145/2529989, p. 1:17, Lemma 3.6

import Mathlib
import Definitions.Def_ApproxMWM_Scaling_Property31

namespace ApproxMWM.Scaling

/-- Lemma 3.6 (Duan–Pettie, J. ACM 61(1) 2014, p. 1:17), for the algorithm of Figure 2 with the
eligibility of Definition 3.2 and integer weights `1 ≤ w(e) ≤ N = 2^L`.
(1) For `i < L`, every edge that is eligible when the algorithm searches `G_elig` in some scale
`j ≤ i` (the Augmentation search at the start of an iteration, or the Blossom Shrinking search
after augmentation) has weight at least `N / 2^{i+1} + δ_i`.
(2) At every scale `i`, every matched edge `e` satisfies `yz(e) ≤ (1 + 4ε') w(e)`. -/
theorem eligible_weight_and_matched_tightness {V : Type*} [Fintype V] [DecidableEq V]
    (P : Params) (G : SimpleGraph V) (w : Sym2 V → ℕ)
    (hw : ∀ e ∈ G.edgeSet, 1 ≤ w e ∧ w e ≤ 2 ^ P.L) :
    (∀ i : ℕ, i < P.L → ∀ j : ℕ, j ≤ i → ∀ s : State V, Reach P G (elig32 P G w) j s →
        P.target j < s.yfree →
        (∀ e : Sym2 V, elig32 P G w j s e → P.N / 2 ^ (i + 1) + P.δ i ≤ (w e : ℝ)) ∧
        ∀ s₁ : State V, Augment G (elig32 P G w j s) j s s₁ →
          ∀ e : Sym2 V, elig32 P G w j s₁ e → P.N / 2 ^ (i + 1) + P.δ i ≤ (w e : ℝ)) ∧
    (∀ (i : ℕ) (s : State V), Reach P G (elig32 P G w) i s →
        ∀ e ∈ s.M, yz s.y s.z e ≤ (1 + 4 * P.eps') * (w e : ℝ)) := by sorry

end ApproxMWM.Scaling
