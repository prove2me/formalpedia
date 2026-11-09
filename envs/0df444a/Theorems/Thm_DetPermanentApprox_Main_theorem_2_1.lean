-- Prove2me | Theorems.Thm_DetPermanentApprox_Main_theorem_2_1
-- name    : DetPermanentApprox.Main.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:26:40.884408+00:00
-- url     : https://prove2.me/theorems/e2b5d8c3-caa9-462f-93dd-9028e8e7ff1e
-- title:
--   Theorem 2.1 — Full entropy interpolation sandwich
-- statement:
--   Let $n\ge1$, let $A\in\mathbb R_{\ge0}^{n\times n}$ have positive permanent, and let $0<t<1$. If $F_A(t)$ maximizes entropy plus expected log matching weight over laws covering every vertex with probability $t$, and $h(t)=-t\log t-(1-t)\log(1-t)$, then
--
--   $$t\log\operatorname{per}A+nh(t)\le F_A(t)\le t\log\operatorname{per}A+2nh(t).$$
--
--   Both constants and both directions are retained. The feasible laws are taken on the original positive support; no total-support hypothesis is imposed. Under equal positive vertex marginals, dead edges have zero inclusion probability, so deletion of such edges does not change this maximum. This is the interpolation statement used to transfer an entropy estimate to the permanent.
--
--   Differences from the source:
--   - encoding: finite labelled matrix, graph, and coordinate sets → Fin n or arbitrary finite types with explicit row and column copies; reason: finite enumerations and reindexing preserve every source instance
--   - encoding: permanent summed over row-to-column permutations → Mathlib matrix permanent with the inverse permutation convention; reason: reindexing the finite sum by permutation inversion gives exactly the source value
--   - encoding: the maximum of entropy plus energy on V_t → a real supremum on the same finite-dimensional feasible-law set; reason: positive permanent makes V_t nonempty and compact, and the continuous objective attains a finite maximum, so the values agree
--   - encoding: F_A(t) on the support after deleting edges in no perfect matching → F_A(t) on the original positive support; reason: equal vertex marginals divided by t form a fractional perfect matching; dead edges therefore have zero inclusion probability and zero law mass on every containing matching, so deletion preserves all feasible objective values
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #704 (October 2026), Theorem 2.1, p. 6 (PDF p. 6); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/704.pdf

import Mathlib
import Definitions.Def_DetPermanentApprox_Main_Matchings

namespace DetPermanentApprox.Main

theorem theorem_2_1 {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hp : 0 < A.permanent)
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    t * Real.log A.permanent + n * binaryEntropy t ≤ F A t ∧
      F A t ≤ t * Real.log A.permanent + 2 * n * binaryEntropy t := by sorry

end DetPermanentApprox.Main
