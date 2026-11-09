-- Prove2me | Theorems.Thm_DetPermanentApprox_Main_lemma_2_4
-- name    : DetPermanentApprox.Main.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:26:30.920049+00:00
-- url     : https://prove2.me/theorems/2188f39a-124a-445a-a5f0-489a9d20fb09
-- title:
--   Lemma 2.4 — Partition function at a minimizer
-- statement:
--   Let $n\ge1$ and let $A\ge0$ have positive permanent and every support edge in a perfect matching. For $0<t<1$, every global minimizer $\theta_t$ of the actual dual objective satisfies
--
--   $$0\le\log Z_G(w_A(\theta_t))\le-2n\log(1-t).$$
--
--   The partition function includes the empty matching. This bounds the partition contribution at every minimizer, with the exact source constant and logarithmic argument.
--
--   Differences from the source:
--   - encoding: finite labelled matrix, graph, and coordinate sets → Fin n or arbitrary finite types with explicit row and column copies; reason: finite enumerations and reindexing preserve every source instance
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #704 (October 2026), Lemma 2.4, p. 9 (PDF p. 9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/704.pdf

import Mathlib
import Definitions.Def_DetPermanentApprox_Main_Matchings

namespace DetPermanentApprox.Main

theorem lemma_2_4 {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hp : 0 < A.permanent) (hs : TotalSupport A)
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (θ : Vertex n → ℝ) (hθ : IsMinimizer (Phi A t) θ) :
    0 ≤ Real.log (Z (supportGraph A) (fieldWeights (supportGraph A) (supportWeights A) θ)) ∧
    Real.log (Z (supportGraph A) (fieldWeights (supportGraph A) (supportWeights A) θ)) ≤
      -2 * n * Real.log (1 - t) := by sorry

end DetPermanentApprox.Main
