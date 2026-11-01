-- Prove2me | Theorems.Thm_DilatableEntropy_dge_min_uniform
-- name    : DilatableEntropy.dge_min_uniform
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:55:13.585187+00:00
-- url     : https://prove2.me/theorems/32b374e8-6883-4cc1-9a54-1edacbf15b3e
-- title:
--   Proof of Theorem 4 — $\min_Q\tilde\varphi=0$, attained exactly at the uniform strategy
-- statement:
--   Let $(J,(A_j)_{j\in J},(p_j)_{j\in J})$ be a sequential decision problem: a finite set $J$ of decision points, a finite nonempty action set $A_j$ at each $j$, and parent sequences $p_j\in\Sigma$ under which the decision points form a tree. $\Sigma=\{\varnothing\}\cup\{ja\}$ is the set of sequences and $Q\subseteq\mathbb R^{\Sigma}$ the sequence-form polytope.
--
--   The dilatable global entropy is nonnegative on $Q$, and its minimum $0$ is attained exactly at the **uniform strategy** $m\in Q$, which assigns probability $1/|A_j|$ to each action at each decision point:
--   $$
--   m_\varnothing=1,\qquad m_{ja}=\frac{m_{p_j}}{|A_j|}\quad(ja\in\Sigma),\qquad \tilde\varphi(m)=0,
--   $$
--   $$
--   \tilde\varphi(x)\ge0\ \text{ for all }x\in Q,\qquad \operatorname*{arg\,min}_{x\in Q}\tilde\varphi(x)=\{m\}.
--   $$
--
--   This is the normalization $\min_Q d=0$ of Definition 1, and $m$ is the prox center used by EGT and mirror prox.
--
--   **Formalization Note** The uniform strategy is described by its recursion: the statement asserts that a point $m\in Q$ with $m_{ja}=m_{p_j}/|A_j|$ exists, that $\tilde\varphi(m)=0$, and that every zero of $\tilde\varphi$ on $Q$ equals $m$ (with nonnegativity, $m$ is the unique minimizer).
--
--   Differences from the source:
--   - encoding: arg min_Q φ̃ = arg min_Q φ = ∇φ*(0) = m is the uniform strategy (p.12) → ∃ m ∈ Q with m_ja = m_pj / |A_j| for all ja, φ̃(m) = 0, and every zero of φ̃ on Q equals m; reason: the two middle sets are equal to the first by Theorem 3 and the definition of ∇d* (p.4); the recursion from m_∅ = 1 determines m uniquely, so the ∃ names the uniform strategy; with φ̃ ≥ 0, the zeros are the minimizers
--   - encoding: a set of decision points J forming a tree, actions A_j, parent sequences p_j, sequences Σ = {∅} ∪ {ja} (pp.7–8) → SeqDecisionProblem: finite J, finite nonempty A j, parent : J → Option (Σ j, A j), well-founded child relation; Σ = Option (Σ j, A j); reason: every finite tree-form decision problem of the paper is such a structure and conversely (each j has one parent sequence, so the C_ja are disjoint); nonempty A_j only excludes the undefined log|A_j| = log 0 and the absence of any strategy at j
-- source:
--   Farina, Kroer, Sandholm, Better Regularization for Sequential Decision Spaces, arXiv:2105.12954v2, proof of Theorem 4, p.12 (arg min_Q φ̃ = m, φ̃(m) = 0), with Definition 4, p.10 (codomain ℝ≥0)

import Mathlib
import Definitions.Def_DilatableEntropy_seqFormPolytope
import Definitions.Def_DilatableEntropy_dge

namespace DilatableEntropy

/-- Farina, Kroer, Sandholm, *Better Regularization for Sequential Decision Spaces*, arXiv:2105.12954v2, proof of Theorem 4, p.12 (the minimum of `φ̃`): `φ̃ ≥ 0` on `Q` (the codomain
`ℝ_{≥0}` of Definition 4), and `argmin_{x ∈ Q} φ̃(x) = m` is the uniform strategy, the point of
`Q` with `m_{ja} = m_{p_j} / |A_j|` for every sequence `ja`, with `φ̃(m) = 0`.

**Formalization Note** The uniform strategy is described by its defining recursion
(`m ∈ Q`, so `m_∅ = 1`); the conclusion asserts that it exists, that `φ̃(m) = 0`, and that it is
the only zero (hence the only minimizer) of `φ̃` on `Q`. -/
theorem dge_min_uniform (P : SeqDecisionProblem) :
    (∀ x ∈ seqFormPolytope P, 0 ≤ dge P x) ∧
      ∃ m ∈ seqFormPolytope P,
        (∀ (j : P.J) (a : P.A j),
            m (some ⟨j, a⟩) = m (P.parent j) / (Fintype.card (P.A j) : ℝ)) ∧
          dge P m = 0 ∧ ∀ x ∈ seqFormPolytope P, dge P x = 0 → x = m := by sorry

end DilatableEntropy
