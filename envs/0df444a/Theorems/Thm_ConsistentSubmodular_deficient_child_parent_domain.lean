-- Prove2me | Theorems.Thm_ConsistentSubmodular_deficient_child_parent_domain
-- name    : ConsistentSubmodular.deficient_child_parent_domain
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:19:21.615614+00:00
-- url     : https://prove2.me/theorems/8c4430d0-7ab4-454a-8876-97f229224953
-- title:
--   Parameter domain for a deficient child with a failed parent
-- statement:
--   Let $d_0,e,W,b,L,k\in\mathbb{R}$ satisfy
--
--   * $d_0\ge0$, $e\ge0$, and $d_0+e\le\tfrac14$;
--   * $2d_0\le L\le b$;
--   * $1\le k<3$;
--   * (attainment) $(3-k)\,W=k\,e+b+3d_0$;
--   * (deficiency) $b+W+e<3(d_0+e)$;
--   * (failure) $k\,(b+W)<2(1-d_0)\,k-3(1-4d_0)$.
--
--   Then
--   $$\tfrac43<k,\qquad k<2,\qquad d_0<\tfrac18 .$$
--
--   This pins down the admissible range of the ratio parameter $k$ and of the parent deficit $d_0$ when a deficient child arises from a failed parent, in the baseline-upgrade step of the deterministic certificates (Appendix B).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/BaselineUpgrade.lean#L79-L101 (`ConsistentSubmodular.deficient_child_parent_domain`)

import Mathlib

theorem ConsistentSubmodular.deficient_child_parent_domain (d₀ e W b L k : ℝ)
    (hd : 0 ≤ d₀) (he : 0 ≤ e) (hchild : d₀ + e ≤ 1 / 4)
    (hL : 2 * d₀ ≤ L) (hLb : L ≤ b) (hk1 : 1 ≤ k) (hk3 : k < 3)
    (hatt : (3 - k) * W = k * e + b + 3 * d₀)
    (hdeficient : b + W + e < 3 * (d₀ + e))
    (hfailed : k * (b + W) < 2 * (1 - d₀) * k - 3 * (1 - 4 * d₀)) :
    (4 : ℝ) / 3 < k ∧ k < 2 ∧ d₀ < 1 / 8 := by sorry
