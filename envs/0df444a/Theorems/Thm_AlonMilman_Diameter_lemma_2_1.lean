-- Prove2me | Theorems.Thm_AlonMilman_Diameter_lemma_2_1
-- name    : AlonMilman.Diameter.lemma_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:27:02.127153+00:00
-- url     : https://prove2.me/theorems/86f5e882-c61d-44e3-9a28-947475648078
-- title:
--   Lemma 2.1 — $\lambda_1 n \le \rho^{-2}(1/a + 1/b)(|E| - |E_A| - |E_B|)$
-- statement:
--   Let $G = (V, E)$ be a connected finite simple graph on $n \ge 2$ vertices and $\lambda_1 = \lambda_1(G)$ the second-smallest eigenvalue of its Laplacian. Let $A, B \subseteq V$ be nonempty, and let $\rho \ge 1$ be an integer such that every vertex of $A$ is at graph distance at least $\rho$ from every vertex of $B$ (in particular $A$ and $B$ are disjoint). Put $a = |A|/n$, $b = |B|/n$, and let $E_A$ ($E_B$) be the set of edges with both endpoints in $A$ (in $B$). Then
--   $$
--   \lambda_1 \cdot n \le \frac{1}{\rho^2}\Big(\frac1a + \frac1b\Big)\big(|E| - |E_A| - |E_B|\big).
--   $$
--
--   This is the main tool of the section: a large $\lambda_1$ forces many edges outside two far-apart sets, relative to their sizes. Theorem 2.5, Remark 2.3 and through them Theorems 2.6 and 2.7 are derived from it.
--
--   **Formalization Note** The paper takes $\rho$ to be the distance between $A$ and $B$; the Lean statement takes any integer $\rho \ge 1$ bounding all pairwise distances from below. Since the right-hand side decreases in $\rho$, the two versions are equivalent. $A$ and $B$ are required nonempty so that $a, b > 0$ (Lean's $1/0 = 0$ would otherwise change the statement). Distances are Mathlib's `SimpleGraph.dist`; all counts are cast to $\mathbb R$ before subtracting.
-- source:
--   Alon, Milman, λ1, Isoperimetric Inequalities for Graphs, and Superconcentrators, J. Combin. Theory Ser. B 38 (1985), p. 77, Lemma 2.1 (with the setup paragraph preceding it)

import Mathlib
import Definitions.Def_AlonMilman_Diameter_lambda1
import Definitions.Def_AlonMilman_Diameter_edgesWithin

namespace AlonMilman.Diameter

theorem lemma_2_1 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) (hn : 2 ≤ Fintype.card V)
    (A B : Finset V) (hA : A.Nonempty) (hB : B.Nonempty) (ρ : ℕ) (hρ : 1 ≤ ρ)
    (hdist : ∀ u ∈ A, ∀ v ∈ B, ρ ≤ G.dist u v) :
    lambda1 G * (Fintype.card V : ℝ) ≤
      (1 / (ρ : ℝ) ^ 2) *
        (1 / ((A.card : ℝ) / Fintype.card V) + 1 / ((B.card : ℝ) / Fintype.card V)) *
        ((G.edgeFinset.card : ℝ) - ((edgesWithin G A).card : ℝ) - ((edgesWithin G B).card : ℝ)) := by sorry

end AlonMilman.Diameter
