-- Prove2me | Theorems.Thm_CaiZhuInfo_Matrix_directed_cycle_entropy
-- name    : CaiZhuInfo.Matrix.directed_cycle_entropy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:16:55.603472+00:00
-- url     : https://prove2.me/theorems/2fd7f944-9f7e-4fd7-9787-392e94d23ab0
-- title:
--   Lemma B.1 — Directed-cycle entropy bound
-- statement:
--   For $n\ge1$, let $P$ be any probability law on $\mathbb Z_n$. For clockwise distance $c(s,r)=(r-s)\bmod n$, set $d_r=\mathbb E_{S\sim P}c(S,r)$. Then
--   $$2^{H(P)}\sum_{r\in\mathbb Z_n}2^{-d_r}\le6+4\sqrt2.$$
--   The case $n=1$ is included, with its only distance equal to zero. This is the cycle entropy estimate used in the threshold-sum milestone.
--
--   Differences from the source:
--   - encoding: the cyclic set Z_n and clockwise modular distance → Fin n and (r+n-s) mod n; reason: for s,r<n the natural subtraction is untruncated and gives the same residue
-- source:
--   Xiaohong Cai, Mingyang Zhu, STOC 2027 submission #616 (October 2026), Lemma B.1, (51), printed p.27 / PDF p.28; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/616.pdf

import Mathlib
import Definitions.Def_CaiZhuInfo_Matrix_LayerData

open MeasureTheory
open scoped Classical ENNReal

namespace CaiZhuInfo.Matrix

theorem directed_cycle_entropy (n : ℕ) (hn : 0 < n) (P : PMF (Fin n)) :
    (2 : ℝ) ^ finiteEntropy P *
      (∑ r : Fin n, (2 : ℝ) ^ (-mean P (fun s => (cycleDistance s r : ℝ)))) ≤
      6 + 4 * Real.sqrt 2 := by sorry

end CaiZhuInfo.Matrix
