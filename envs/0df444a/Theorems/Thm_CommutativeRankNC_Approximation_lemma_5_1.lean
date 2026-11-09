-- Prove2me | Theorems.Thm_CommutativeRankNC_Approximation_lemma_5_1
-- name    : CommutativeRankNC.Approximation.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:54:08.672916+00:00
-- url     : https://prove2.me/theorems/3086d202-a620-4322-8870-e5ba4a5359c1
-- title:
--   Lemma 5.1 — Universal bounded rational directions
-- statement:
--   For every fixed integer $k\ge1$, the explicitly constructed family $D_{k,m}\subseteq\mathbb Q^m$ has polynomial size in $m$ and one deterministic logspace-uniform Boolean NC² enumerator. It is fixed before any matrix tuple or current matrix is chosen. For every rational matrix space $\mathcal B$ and $A\in\mathcal B$, a shared normalization exists, and for every such normalization some $b\in D_{k,m}$ satisfies
--
--   $$\operatorname{rank}_{\mathbb Q}J_k(A,B(b))\ge\beta_k\operatorname{rank}_{\mathbb Q(x)}J_k(A,B(x)),\qquad\beta_k=(3/50)^k.$$
--
--   Every reduced coordinate numerator has absolute value at most $k$ and every positive denominator is at most $k$. The image defining $D_{k,m}$ retains the $b_0=0$ branch. Polynomial and circuit constants depend only on $k$.
--
--   Differences from the source:
--   - generalization: the positive-dimensional matrix setting → also zero-dimensional matrices and empty generating lists; reason: the zero matrix and empty blocks supply these extra cases without excluding any source instance
--   - encoding: the same invertible row and column transformations applied to A and all directions → Normalization data containing rational matrix units, the rank, and the diagonal identity; reason: the normalized matrices are the source objects; they are analysis data and never input advice to the headline algorithm
--   - encoding: one-based matrix and variable indices → zero-based finite index types and ordered pairs for truncated blocks; reason: the same entries and blocks are present under a bijective reindexing
--   - encoding: polynomial-size parallel computable family with βₖ=c₀ᵏ/2ᵏ → the exact dehomogenized image, a seed-indexed Boolean NC² output table, and βₖ=(3/50)ᵏ; reason: the construction on p.27 gives this same image and constant, including zero homogenizing coordinate; duplicates only repeat family members
-- source:
--   Foram Lakhani, Partha Mukhopadhyay, STOC 2027 submission #458 (October 2026), Lemma 5.1, PDF/printed p.21; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/458.pdf

import Definitions.Def_CommutativeRankNC_Approximation_ConstructionCodes

namespace CommutativeRankNC.Approximation

/-- Lemma 5.1, PDF/printed p.21, construction pp.24–27. The common family is
fixed by k,m before all matrix tuples and current matrices. Enumeration has
uniform Boolean NC² bounds, and reduced numerators/denominators are bounded. -/
theorem lemma_5_1 (k : ℕ) (hk : 0 < k) :
    ∃ F : (N : ℕ) → BooleanCircuit N, BooleanNC 2 F ∧
      ∃ C d : ℕ, 0 < C ∧ ∀ m : ℕ,
        (directionFamily k m).card ≤ C * (m+2)^d ∧
        booleanEval (F m) (List.replicate m true) = directionTableCode k m ∧
        (∀ b ∈ directionFamily k m, ∀ i,
          (b i).num.natAbs ≤ k ∧ (b i).den ≤ k) ∧
        ∀ (n : ℕ) (B : Fin m → QMatrix n) (A : QMatrix n), A ∈ matrixSpace B →
          Nonempty (Normalization A) ∧ ∀ S : Normalization A,
            ∃ b ∈ directionFamily k m,
              beta k * ((genericJ S B k).rank : ℝ) ≤
                ((scalarJ S (pencilEval B b) k).rank : ℝ) := by sorry

end CommutativeRankNC.Approximation
