-- Prove2me | Theorems.Thm_BFAlmostLinear_lemma_2_2
-- name    : BFAlmostLinear.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:40:55.989884+00:00
-- url     : https://prove2.me/theorems/6380eef7-1fa8-442c-80e4-11169333d512
-- title:
--   Lemma 2.2 — $|\mathcal X_\phi\cap\mathcal Y|\le O(\frac{n^2}{\ell}\cdot\frac{b\log^3 n}{\log\log n})$ whp
-- statement:
--   Let $G$ be a weighted graph on $n\ge3$ vertices with frozen flags, $N$ a set of vertices, $b\ge1$ and hop bounds $h_1,h_2$. Let $U\subseteq N$ contain each vertex of $N$ independently with probability $1/b$. For every $c>0$ there is $K$ such that with probability at least $1-n^{-c}$ over $U$: for every real $\ell\ge1$ and every $\mathcal Y\subseteq V\times N\times V$ with
--   1. $|\mathcal Y[*,r,*]|\le n^2/\ell^2$ for all $r\in N$,
--   2. $|\mathcal Y[s,r,*]|\le n/\ell$ for all $s\in V$, $r\in N$,
--   3. $|\mathcal Y[*,r,t]|\le n/\ell$ for all $r\in N$, $t\in V$,
--
--   and every potential $\phi$ that fixes $U$,
--   $$|\mathcal X_\phi\cap\mathcal Y|\le K\,\frac{n^2}{\ell}\cdot\frac{b\log^3 n}{\log\log n}.$$
--
--   This is the paper's main technical lemma; Theorem 2.1 follows from it by peeling.
--
--   Differences from the source:
--   - generalization: one hop bound $h$ → a pair $(h_1,h_2)$; reason: Lemma 4.6's proof (p.18) needs $d^0+d^1$; $h_1=h_2$ is the printed form.
--   - generalization: $N$ the negative vertices → any set of vertices; reason: the proof only uses the sampling of $U$ from $N$.
--   - encoding: "with high probability", $O(\cdot)$ → $\forall c>0\ \exists K$, probability $\ge1-n^{-c}$, explicit constant $K$; reason: footnote 2, p.1.
--   - encoding: $n\ge3$; reason: $\log\log n\le0$ for $n\le2$.
--   - encoding: frozen-flag convention → hypothesis `Frozen`; reason: §1.1, p.2.
-- source:
--   Hair, Li, Li, Zhang, Bellman-Ford in Almost-Linear Time, STOC 2027 submission (manuscript sha256 873b9acb…), Lemma 2.2, p.6 (restated p.8)

import Mathlib
import Definitions.Def_BFAlmostLinear_WGraph
import Definitions.Def_BFAlmostLinear_sampleMass

namespace BFAlmostLinear

open Classical in
/-- **Lemma 2.2**, p.6 (restated p.8). "Let U ⊆ N be a random sample where each vertex in N is sampled with
probability 1/b. With high probability over the randomness of U, the following holds. Consider any parameter
ℓ ≥ 1 and any subset Y ⊆ V × N × V such that 1. |Y[∗, r, ∗]| ≤ n²/ℓ² for all r ∈ N, 2. |Y[s, r, ∗]| ≤ n/ℓ for all s ∈ V
and r ∈ N, and 3. |Y[∗, r, t]| ≤ n/ℓ for all r ∈ N and t ∈ V. Then, for any potential function ϕ that fixes U, we have
|X_ϕ ∩ Y| ≤ O((n²/ℓ) · b log³ n / log log n)."

Hair, Li, Li, Zhang, *Bellman-Ford in Almost-Linear Time*, STOC 2027 submission (manuscript sha256
873b9acb…), Lemma 2.2, p.6.

**Formalization Note.** `ℓ` is real, as printed. Generalized to a hop pair `(h₁, h₂)`, with `N` any set of vertices.
The good event comes before `ℓ`, `Y` and `ϕ`. `n ≥ 3` makes `log log n > 0`. -/
theorem lemma_2_2 :
    ∀ c : ℝ, 0 < c → ∃ K : ℝ, 0 < K ∧
      ∀ (V E : Type) [Fintype V] [Fintype E] (G : WGraph V E) (N : Finset V) (b : ℝ) (h₁ h₂ : ℕ),
        G.Frozen → 1 ≤ b → 3 ≤ Fintype.card V →
        1 - (Fintype.card V : ℝ) ^ (-c) ≤
          goodMass N b fun U =>
            ∀ (ℓ : ℝ) (Y : Finset (V × V × V)), 1 ≤ ℓ → (∀ x ∈ Y, x.2.1 ∈ N) →
              (∀ r ∈ N, (((Y.filter fun x => x.2.1 = r).card : ℕ) : ℝ) ≤
                (Fintype.card V : ℝ) ^ 2 / ℓ ^ 2) →
              (∀ s, ∀ r ∈ N, (((Y.filter fun x => x.1 = s ∧ x.2.1 = r).card : ℕ) : ℝ) ≤
                (Fintype.card V : ℝ) / ℓ) →
              (∀ r ∈ N, ∀ t, (((Y.filter fun x => x.2.1 = r ∧ x.2.2 = t).card : ℕ) : ℝ) ≤
                (Fintype.card V : ℝ) / ℓ) →
              ∀ ϕ : V → ℝ, G.Fixes h₁ h₂ U ϕ →
                (((Y.filter fun x => G.InX h₁ h₂ ϕ x.1 x.2.1 x.2.2).card : ℕ) : ℝ) ≤
                  K * ((Fintype.card V : ℝ) ^ 2 / ℓ) *
                    (b * Real.log (Fintype.card V) ^ 3 / Real.log (Real.log (Fintype.card V))) := by sorry

end BFAlmostLinear
