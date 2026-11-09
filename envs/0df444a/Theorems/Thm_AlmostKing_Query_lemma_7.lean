-- Prove2me | Theorems.Thm_AlmostKing_Query_lemma_7
-- name    : AlmostKing.Query.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:51:44.492199+00:00
-- url     : https://prove2.me/theorems/7bde41a0-8744-405e-b266-28b1a4a8a6ab
-- title:
--   Lemma 7 — four properties of template orientations
-- statement:
--   For every $0<\eta\le1/16$, there are $\alpha,\kappa\in(0,1)$, positive constants $M,C$, and a threshold $N_0$, all depending only on $\eta$. For every $n\ge N_0$, every $\kappa$-template graph $G$ on $n$ vertices, and every orientation $D$ of $G$, there are a partition $V_0,V_1,\ldots,V_r$, nonempty equal-sized groups $V_i$, and courts $A_i\subseteq V_i$ with common size $L$ such that:
--
--   1. With $|V_i|=\ell$,
--   $$|V_0|\le\eta n,\qquad\lceil1/\eta\rceil\le r\le M.$$
--   2. For the computed group graph $R=R(D,P)$ with parameters $\alpha$ and $p=n^{-2/3}$,
--   $$|\{\{i,j\}:i\ne j,\ i\not\to j,\ j\not\to i\text{ in }R\}|\le\eta r^2.$$
--   3. The courts satisfy
--   $$|A_i|=L,\qquad 1/\eta\le L\le C n^{2/3}.$$
--   4. For every arc $i\to j$ of $R$ and every $Z\subseteq A_i$ with $|Z|\ge\eta L$,
--   $$|N_D^+(Z)\cap V_j|\ge(1-\eta)\ell.$$
--
--   All objects in the conclusion depend on the given orientation alone; no unknown tournament completion occurs in the statement. This is the full structural interface required by the main result.
--
--   Differences from the source:
--   - encoding: $[n]=\{1,\ldots,n\}$ → $\mathrm{Fin}\,n=\{0,\ldots,n-1\}$; reason: relabeling by an order-preserving bijection preserves all graph and counting conditions
--   - reading: $r=O_\eta(1)$ and $L=O_\eta(n^{2/3})$, for sufficiently large $n$ → positive constants $M,C$ and a threshold before $n,G,D$; reason: these are explicit uniform bounds with dependence only on $\eta$
--   - encoding: unordered missing index pairs and nonempty groups → pairs represented once by $i<j$, and explicit nonemptiness of every group; reason: this is the source count and the domain condition of Definition 6; nonemptiness also follows from the positive court size
-- source:
--   Ziad Ismaili Alaoui, Oded Lachish, Nikhil S. Mande, A King for Almost Everyone, STOC 2027 submission #472 (October 2026), SHA-256 c262b203b2088dcae48025a77e016df4cc78f93c1856a6fac580c7577d8dea92, Lemma 7, p. 7. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/472.pdf

import Mathlib
import Definitions.Def_AlmostKing_Query_Regularity

open Classical

namespace AlmostKing.Query

/-- Lemma 7, p. 7, all four properties; constants are uniform in n, G, and D. -/
theorem lemma_7 : ∀ η : ℝ, 0 < η → η ≤ (1 : ℝ) / 16 →
    ∃ α κ : ℝ, 0 < α ∧ α < 1 ∧ 0 < κ ∧ κ < 1 ∧
    ∃ M C : ℝ, 0 < M ∧ 0 < C ∧ ∃ N₀ : ℕ,
    ∀ n : ℕ, N₀ ≤ n → ∀ G : SimpleGraph (Fin n), IsTemplate κ G →
    ∀ D : Digraph (Fin n), IsOrientation G D →
    ∃ r ℓ L : ℕ, ∃ V₀ : Finset (Fin n),
    ∃ groups A : Fin r → Finset (Fin n),
      IsPartition V₀ groups ∧ (∀ i, (groups i).Nonempty) ∧
      (V₀.card : ℝ) ≤ η * n ∧ (∀ i, (groups i).card = ℓ) ∧
      ⌈1 / η⌉₊ ≤ r ∧ (r : ℝ) ≤ M ∧
      (missingPairs (groupGraph D groups α ((n : ℝ) ^ (-(2 : ℝ) / 3))) : ℝ) ≤
        η * (r : ℝ)^2 ∧
      (∀ i, A i ⊆ groups i ∧ (A i).card = L) ∧
      1 / η ≤ (L : ℝ) ∧ (L : ℝ) ≤ C * (n : ℝ) ^ ((2 : ℝ) / 3) ∧
      ∀ i j, (groupGraph D groups α ((n : ℝ) ^ (-(2 : ℝ) / 3))).Adj i j →
        ∀ Z : Finset (Fin n), Z ⊆ A i → η * L ≤ (Z.card : ℝ) →
          (1 - η) * ℓ ≤ (((outNbhdSet D Z) ∩ groups j).card : ℝ) := by sorry

end AlmostKing.Query
