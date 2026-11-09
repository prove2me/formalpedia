-- Prove2me | Theorems.Thm_DetPermanentApprox_Main_lemma_3_5
-- name    : DetPermanentApprox.Main.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:28:34.871705+00:00
-- url     : https://prove2.me/theorems/2bd5a3e0-783b-4742-86af-46a26642a251
-- title:
--   Lemma 3.5 — Zero-free disk and first and second derivative bounds
-- statement:
--   Let $G$ be any finite simple graph on $N\ge2$ vertices, let rational $K\ge1$, and let $y\in D_K$. Every induced subgraph satisfies $Z_H(\tau(z)e^y)\ne0$ for $|z|<1$. The full graph has a holomorphic logarithm $F_y$ on that disk with $F_y(0)=0$ and $e^{F_y(z)}=Z_G(\tau(z)e^y)$. For every edge $e$, every sign vector $\sigma\in\{-1,1\}^E$, and $|z|\le R=(1+z_\star)/2$,
--
--   $$|\partial_eF_y(z)|\le9e^{y_e},\qquad |D_\sigma\partial_eF_y(z)|\le400Ke^{y_e}.$$
--
--   Derivatives are in full ambient logarithmic-weight space. This provides zero-freeness and both derivative controls, with neither a principal-log convention nor a bipartite restriction.
--
--   Differences from the source:
--   - encoding: finite labelled matrix, graph, and coordinate sets → Fin n or arbitrary finite types with explicit row and column copies; reason: finite enumerations and reindexing preserve every source instance
--   - encoding: a normalized holomorphic logarithm and its log-weight derivatives → the radial logarithmic-derivative integral, with holomorphy, normalization and exponential identity asserted as conclusions; reason: on the zero-free disk this is exactly the unique normalized logarithm and has a smooth local extension in y
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #704 (October 2026), Lemma 3.5, p. 16 (PDF p. 16); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/704.pdf

import Mathlib
import Definitions.Def_DetPermanentApprox_Main_Analysis

namespace DetPermanentApprox.Main

theorem lemma_3_5 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (hG : IsSimple G) (hN : 2 ≤ Fintype.card V)
    (K : ℚ) (hK : 1 ≤ K) (y : E → ℝ) (hy : y ∈ degreeRegion G (K : ℝ)) :
    (∀ (S : Finset V) (z : ℂ), ‖z‖ < 1 →
      complexZ G S (fun e => tau K z * (Real.exp (y e) : ℂ)) ≠ 0) ∧
    DifferentiableOn ℂ (normalizedLog G K y) (Metric.ball 0 1) ∧
    normalizedLog G K y 0 = 0 ∧
    (∀ z : ℂ, ‖z‖ < 1 → Complex.exp (normalizedLog G K y z) = transformedPartition G K y z) ∧
    (∀ (e : E) (σ : E → ℝ) (z : ℂ), (∀ f, σ f = -1 ∨ σ f = 1) → ‖z‖ ≤ radius K →
      ‖partialC (fun y' => normalizedLog G K y' z) y e‖ ≤ 9 * Real.exp (y e) ∧
      ‖∑ f, (σ f : ℂ) * partialC
        (fun y' => partialC (fun y'' => normalizedLog G K y'' z) y' e) y f‖ ≤
          400 * (K : ℝ) * Real.exp (y e)) := by sorry

end DetPermanentApprox.Main
