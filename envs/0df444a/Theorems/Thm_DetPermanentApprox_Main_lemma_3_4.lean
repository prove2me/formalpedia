-- Prove2me | Theorems.Thm_DetPermanentApprox_Main_lemma_3_4
-- name    : DetPermanentApprox.Main.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:29:39.286202+00:00
-- url     : https://prove2.me/theorems/da2991fe-8538-486c-be50-46f960980dca
-- title:
--   Lemma 3.4 — Path-tree resolvent and operator norm
-- statement:
--   Let $G$ be a finite simple graph on $N\ge2$ vertices with positive edge weights $w$, and let $H$ be any induced subgraph with root $v$. Let $B$ be its weighted path-tree matrix, with extension entries $\sqrt{w_e}$, and let $r$ be its length-one root. For complex $s$, whenever the partition denominator is nonzero and $I+sB^2$ is invertible,
--
--   $$\frac{Z_{H-v}(sw)}{Z_H(sw)}=[(I+sB^2)^{-1}]_{rr}.$$
--
--   If $K\ge1$ is rational, $w=e^y$ and $y\in D_K$, then $\|B\|_2\le2\sqrt K$. This retains the resolvent identity and the exact Euclidean norm bound.
--
--   Differences from the source:
--   - encoding: finite labelled matrix, graph, and coordinate sets → Fin n or arbitrary finite types with explicit row and column copies; reason: finite enumerations and reindexing preserve every source instance
--   - encoding: induced subgraphs, their path-tree matrices and Euclidean operator norms → vertex subsets, explicitly bounded injective path sequences, and the norm inequality on every vector; reason: this represents the same finite tree and the same Euclidean norm; nonvanishing and determinant-unit guards mean exactly that both sides are defined
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #704 (October 2026), Lemma 3.4, p. 14 (PDF p. 14); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/704.pdf

import Mathlib
import Definitions.Def_DetPermanentApprox_Main_Analysis

namespace DetPermanentApprox.Main

theorem lemma_3_4 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (hG : IsSimple G) (hN : 2 ≤ Fintype.card V)
    (w : E → ℝ) (hw : ∀ e, 0 < w e) (S : Finset V) (v : V) (hv : v ∈ S) :
    let B := pathMatrix G S v w
    let Bc : Matrix (Path G S v) (Path G S v) ℂ := B.map (fun x => (x : ℂ))
    let r := rootPath G S v hv
    (∀ s : ℂ, complexZ G S (fun e => s * (w e : ℂ)) ≠ 0 →
      IsUnit (Matrix.det (1 + s • (Bc * Bc))) →
      complexZ G (S.erase v) (fun e => s * (w e : ℂ)) /
        complexZ G S (fun e => s * (w e : ℂ)) = ((1 + s • (Bc * Bc))⁻¹) r r) ∧
    (∀ (K : ℚ) (y : E → ℝ), 1 ≤ K → y ∈ degreeRegion G (K : ℝ) →
      w = expWeights y → EuclideanBound B (2 * Real.sqrt (K : ℝ))) := by sorry

end DetPermanentApprox.Main
