-- Prove2me | Theorems.Thm_CosetTreeSVP_SVP_lemma_3_2
-- name    : CosetTreeSVP.SVP.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:32:43.644078+00:00
-- url     : https://prove2.me/theorems/481fd5db-7758-4de8-827a-ac3279648180
-- title:
--   Lemma 3.2 — discrete Gaussian tails: P[‖X‖ > C_cσ√n] ≤ 2^{−2cn} and E[‖X‖²1{‖X‖ > C_cσ√n}] ≤ σ²n2^{−cn} for every lattice and σ > 0
-- statement:
--   **Lemma 3.2** ([Hha26, Lemma 2.8]). For every $c > 0$ there is $C_c > 0$ such that for every $n$, every lattice $L \subset \mathbb R^n$ (a discrete additive subgroup) and every $\sigma > 0$,
--   $$\Pr_{X\sim D_{L,\sigma}}\big[\|X\| > C_c\sigma\sqrt n\big] \le 2^{-2cn},\qquad \mathbb E_{X\sim D_{L,\sigma}}\big[\|X\|^2\,\mathbf 1\{\|X\| > C_c\sigma\sqrt n\}\big] \le \sigma^2n\,2^{-cn}.$$
--   It bounds the probability that the SVP algorithm aborts on a long sample.
--
--   Differences from the source:
--   - generalization: 'every lattice L' (§2.1 works with full-rank lattices BZⁿ) → every discrete ℤ-submodule L of ℝⁿ (any rank); reason: the tail bound holds for lattices of any rank; a full-rank BZⁿ (det B ≠ 0) is discrete, so the statement specializes to the paper's
--   - encoding: probability and expectation under D_{L,σ} → sums in [0, ∞] of the weights ρ_σ(x)/ρ_σ(L) over x ∈ L; reason: D_{L,σ} is a discrete law; nonnegative integrands
-- source:
--   Hhan, Finding a Shortest Vector and More in 2^{n/2+o(n)} Time using q-ary Coset Difference Tree, arXiv:2609.02764 (held version, sha256 687602f4…), p. 12 (PDF 14), Lemma 3.2

import Mathlib
import Definitions.Def_SuperlatSVP_lat
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Definitions.Def_RegevLWE_Hyperplane_DiscreteGaussian
import Definitions.Def_CosetTreeSVP_SVP_Basics

open MeasureTheory Filter Topology
open scoped ENNReal

namespace CosetTreeSVP.SVP

theorem lemma_3_2 (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (L : Submodule ℤ (E n)), DiscreteTopology L →
      ∀ σ : ℝ, 0 < σ →
        dgProb L σ {x | C * σ * Real.sqrt n < ‖x‖} ≤
            ENNReal.ofReal ((2 : ℝ) ^ (-(2 * c * n))) ∧
          dgExpect L σ
              (fun x => ENNReal.ofReal (‖x‖ ^ 2) *
                {x : E n | C * σ * Real.sqrt n < ‖x‖}.indicator (fun _ => 1) x) ≤
            ENNReal.ofReal (σ ^ 2 * n * (2 : ℝ) ^ (-(c * n))) := by sorry

end CosetTreeSVP.SVP
