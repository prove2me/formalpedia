-- Prove2me | Theorems.Thm_BHTOpinion_Approx_Supplement_theorem3_stable_iff
-- name    : BHTOpinion.Approx.Supplement.theorem3_stable_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T05:55:30.86282+00:00
-- url     : https://prove2.me/theorems/1cfd9efc-f3df-45f1-bfd6-32a1c11576f0
-- title:
--   Theorem 3 — an equilibrium is stable iff every two clusters are more than 1 + min{W_A,W_B}/max{W_A,W_B} apart
-- statement:
--   Consider $n$ agents with positive weights $w_1,\dots,w_n$ evolving by the weighted system (2.4). Let $s\in F$ be an **equilibrium**: for all $i,j$, either $s_i=s_j$ or $|s_i-s_j|\ge1$. A **cluster** of $s$ is the set of agents sharing one value $a$, with weight $W_a=\sum_{i:s_i=a}w_i$. The equilibrium is **stable** if adding one agent of weight $\delta$ at any opinion moves no original agent by more than $\Delta(\delta,s)$, with $\Delta(\delta,s)\to0$ as $\delta\downarrow0$ (over all perturbing opinions, all times and all solutions).
--
--   **Theorem 3.** The equilibrium $s$ is stable if and only if for any two clusters $A$ and $B$, with values $s_A\neq s_B$ and weights $W_A,W_B$,
--   $$
--   |s_A-s_B| \;>\; d \;=\; 1+\frac{\min\{W_A,W_B\}}{\max\{W_A,W_B\}} .
--   $$
--
--   The inequality is strict: an equilibrium with two clusters exactly at distance $d$ is unstable. For clusters of equal weight the threshold is $2$; unequal weights allow stable intercluster distances below $2$. The theorem explains why simulations of (2.1) typically end with clusters about $2$ apart.
--
--   **Formalization Note** Clusters are indexed by pairs of agents with different values; the condition is required for every such pair (all pairs of clusters, not only adjacent ones). Stability is the predicate `IsStable` of the supplement's weighted-model definition, an $\varepsilon$–$\eta$ form of $\lim_{\delta\downarrow0}\Delta(\delta,s)=0$ in which displacement is measured only for the original agents and every solution counts.
--
--   Differences from the source:
--   - encoding: any two clusters A and B, their distance → every pair of agents i, j with s_i ≠ s_j, distance |s_i − s_j|, weights W at s_i and s_j; reason: clusters of an equilibrium are the distinct values of s; each pair of clusters is reached by a pair of agents
--   - reading: an equilibrium (weights implicit) → s ∈ F with fixed weights w_i > 0; reason: §2.2 sets the theorem in the weighted system (2.4) with mass weights; positivity is the ordinary mass interpretation used by the proof's center of mass, and unit weights are included
--   - reading: Δ(δ, s̃) is a supremum over solutions of the system (2.1) → solutions of the weighted system (2.4) with the new agent of weight δ; reason: the definition is given in the weighted setup of §2.2, with an added agent of weight δ; (2.1) has no weights
-- source:
--   Blondel, Hendrickx, Tsitsiklis, Continuous-time average-preserving opinion dynamics with opinion-dependent communications, SIAM J. Control Optim. 48 (2010), DOI 10.1137/090766188, Theorem 3, p. 5220 (PDF 7); setting (2.4) and stability p. 5220; proof sketch p. 5221 (PDF 8)

import Mathlib
import Definitions.Def_BHTOpinion_Discrete_Model
import Definitions.Def_BHTOpinion_Approx_Supplement_Weighted

namespace BHTOpinion.Approx.Supplement

theorem theorem3_stable_iff {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i : Fin n, 0 < w i)
    (s : Fin n → ℝ) (hs : s ∈ BHTOpinion.Discrete.F n) :
    IsStable w s ↔
      ∀ i j : Fin n, s i ≠ s j →
        1 + min (clusterWeight w s (s i)) (clusterWeight w s (s j)) /
            max (clusterWeight w s (s i)) (clusterWeight w s (s j)) < |s i - s j| := by sorry

end BHTOpinion.Approx.Supplement
