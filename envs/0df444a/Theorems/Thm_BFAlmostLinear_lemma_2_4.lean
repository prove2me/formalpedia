-- Prove2me | Theorems.Thm_BFAlmostLinear_lemma_2_4
-- name    : BFAlmostLinear.lemma_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:40:32.711559+00:00
-- url     : https://prove2.me/theorems/e15abbeb-7cf0-4007-b061-74222bf8ee2b
-- title:
--   Lemma 2.4 — subset betweenness reduction: $|R_\phi|\le O(b\ell\log n)$ whp
-- statement:
--   Let $G$ be a weighted graph on $n$ vertices with frozen flags, $N$ a set of vertices, $b\ge1$, and hop bounds $h_1,h_2$. Let $U\subseteq N$ contain each vertex of $N$ independently with probability $1/b$. For every $c>0$ there is $K$ (independent of the graph) such that with probability at least $1-n^{-c}$ over $U$ the following holds: for every integer $1\le\ell\le n$, all $S,T\subseteq V$ with $|S|=|T|=\ell$, and every potential $\phi$ that fixes $U$,
--   $$\big|\{r\in N : \exists s\in S,\ t\in T,\ d^{h_1}_\phi(s,r)+d^{h_2}_\phi(r,t)<0\}\big|\le K\,b\,\ell\,\log n.$$
--
--   This is the subset betweenness reduction guarantee that Lemma 2.2 bootstraps.
--
--   Differences from the source:
--   - generalization: one hop bound $h$ → a pair $(h_1,h_2)$; reason: Lemma 4.6's proof (p.18) applies §2 to $d^0+d^1$; $h_1=h_2=h$ is the printed form.
--   - generalization: $N$ the negative vertices → $N$ any set of vertices; reason: the proof uses only that $U$ is sampled from $N$.
--   - encoding: "with high probability" → for every $c>0$ there is $K$ with probability $\ge1-n^{-c}$; reason: footnote 2, p.1.
--   - encoding: $O(b\ell\log n)$ → $K b\ell\log n$; reason: Lean form of the $O$.
--   - encoding: the frozen-flag convention → hypothesis that every arc of negative weight is flagged; reason: §1.1 counts all negative edges as hops.
-- source:
--   Hair, Li, Li, Zhang, Bellman-Ford in Almost-Linear Time, STOC 2027 submission (manuscript sha256 873b9acb…), Lemma 2.4, p.7, with the sample of Lemma 2.2, p.6

import Mathlib
import Definitions.Def_BFAlmostLinear_WGraph
import Definitions.Def_BFAlmostLinear_sampleMass

namespace BFAlmostLinear

open Classical in
/-- **Lemma 2.4**, p.7. "With high probability over the randomness of U, the following holds for all integers
ℓ ∈ [n] and all subsets S, T ⊆ V with |S| = |T| = ℓ: for any potential function ϕ that fixes U, the set
R_ϕ = {r : X_ϕ[S, r, T] ≠ ∅} has size at most O(bℓ log n)."

Hair, Li, Li, Zhang, *Bellman-Ford in Almost-Linear Time*, STOC 2027 submission (manuscript sha256
873b9acb…), Lemma 2.4, p.7, with the sample of Lemma 2.2, p.6: "U ⊆ N … each vertex in N is sampled with
probability 1/b".

**Formalization Note.**
* "With high probability" is `∀ c > 0`, a probability at least `1 − n^{−c}`, with `K` chosen after `c`.
* Generalized to a hop pair `(h₁, h₂)`; the printed form is `h₁ = h₂ = h`. `N` is any set of vertices. `b ≥ 1` is a real.
* No lower bound on `n` is needed: for `n ≤ 1` the probability bound `1 − n^{−c}` is at most `0`. -/
theorem lemma_2_4 :
    ∀ c : ℝ, 0 < c → ∃ K : ℝ, 0 < K ∧
      ∀ (V E : Type) [Fintype V] [Fintype E] (G : WGraph V E) (N : Finset V) (b : ℝ) (h₁ h₂ : ℕ),
        G.Frozen → 1 ≤ b →
        1 - (Fintype.card V : ℝ) ^ (-c) ≤
          goodMass N b fun U =>
            ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ Fintype.card V → ∀ S T : Finset V, S.card = ℓ → T.card = ℓ →
              ∀ ϕ : V → ℝ, G.Fixes h₁ h₂ U ϕ →
                (((N.filter fun r => ∃ s ∈ S, ∃ t ∈ T, G.InX h₁ h₂ ϕ s r t).card : ℕ) : ℝ) ≤
                  K * b * ℓ * Real.log (Fintype.card V) := by sorry

end BFAlmostLinear
