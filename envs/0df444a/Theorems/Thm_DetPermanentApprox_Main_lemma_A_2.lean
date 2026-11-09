-- Prove2me | Theorems.Thm_DetPermanentApprox_Main_lemma_A_2
-- name    : DetPermanentApprox.Main.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:31:10.228605+00:00
-- url     : https://prove2.me/theorems/4255d753-85ab-4174-a48e-311ef86783ed
-- title:
--   Lemma A.2 — Decrease of the inexact projected iteration
-- statement:
--   Under the rounded-data and precision conditions of Algorithm 2, let $\theta^*$ be a global minimizer of $\Phi_{C,t}$ in the box $X$. Fix an executed round $k<T$. If the algorithm selects the degree-correction branch, or selects the objective branch with $f(\theta_k)>f(\theta^*)+\eta/2$, then
--
--   $$\|\theta_{k+1}-\theta^*\|_2^2\le\|\theta_k-\theta^*\|_2^2-h\eta/2.$$
--
--   Here $h=\eta/(64n^2)$ and both iterates come from the concrete dyadic-gradient and clipped-update procedure. No accuracy or norm certificate is taken as an input hypothesis.
--
--   Differences from the source:
--   - encoding: finite labelled matrix, graph, and coordinate sets → Fin n or arbitrary finite types with explicit row and column copies; reason: finite enumerations and reindexing preserve every source instance
--   - encoding: Algorithm 2 and the approximation procedures of Appendix A → the explicit Taylor approximation, first eligible vertex, nearest dyadic rounding with upward ties, and coordinatewise clipping; reason: these fix the permitted deterministic choices in the source procedure without assuming their accuracy
--   - encoding: the minimizer from Lemma 4.2 → any actual global dual minimizer lying in the same box; reason: the source selects a bounded minimizer arbitrarily and the argument uses only these properties
--   - generalization: C and p produced by Algorithm 1 preprocessing → any rational C and natural p satisfying RoundedData, with the same Section 4 parameters; reason: every source output satisfies RoundedData; the arguments on pp.21-30 use only its entry, grid, permanent and support properties, without the construction history or the least choice of p
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #704 (October 2026), Lemma A.2, p. 25 (PDF p. 25); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/704.pdf

import Mathlib
import Definitions.Def_DetPermanentApprox_Main_Numerical
import Definitions.Def_DetPermanentApprox_Main_Analysis

namespace DetPermanentApprox.Main

theorem lemma_A_2 {n : ℕ} (hn : 2 ≤ n) (C : Matrix (Fin n) (Fin n) ℚ)
    (p s : ℕ) (hs : 2 ≤ s) (hC : RoundedData C p)
    (θstar : Vertex n → ℝ)
    (hmin : IsMinimizer (Phi (realMatrix C) (targetMarginal s : ℝ)) θstar)
    (hbox : θstar ∈ box n p s) (k : ℕ) (hk : k < iterationCount n p s)
    (hbranch : correctionVertex C p s (iterateTheta C p s k) ≠ none ∨
      (correctionVertex C p s (iterateTheta C p s k) = none ∧
        surrogateObjective C s (fun v => (iterateTheta C p s k v : ℝ)) >
          surrogateObjective C s θstar + (eta s : ℝ) / 2)) :
    squaredNorm (fun v => (iterateTheta C p s (k + 1) v : ℝ) - θstar v) ≤
      squaredNorm (fun v => (iterateTheta C p s k v : ℝ) - θstar v) -
        (stepSize n s : ℝ) * (eta s : ℝ) / 2 := by sorry

end DetPermanentApprox.Main
