-- Prove2me | Theorems.Thm_AESIndependence_Main_balanced_comparison
-- name    : AESIndependence.Main.balanced_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T04:10:10.380071+00:00
-- url     : https://prove2.me/theorems/00d65a16-d358-4e21-a9ec-c70020fa7f0d
-- title:
--   Theorem 2.18 — comparison using balanced simulations
-- statement:
--   Let $K_{\rm ref}$ and $K_{\rm tar}$ act on the same finite space $X$ with at least two elements. Each samples a permutation label independently of its current state, according to its own PMF, and each transition matrix is symmetric, hence reversible with respect to uniform measure. Let $L$ be a positive integer.
--   For each reference label of positive probability, suppose there is a fixed length $\ell_g\le L$ and a distribution on target-label sequences, independent of the input, with exact product equal to that reference permutation. Each position has exactly the target chain’s label law; positions may be correlated. Then
--   $$\operatorname{gap}(K_{\rm tar})\ge\frac{\operatorname{gap}(K_{\rm ref})}{L^2}.$$
--   The two label laws need not be uniform on distinct permutations, and no irreducibility or positivity of either gap is assumed. This retains the source’s precise quadratic comparison loss, including reducible chains.
--
--   Differences from the source:
--   - encoding: finite uniform-reversible permutation-label chains → real matrices from the pushforward of the actual label PMF, symmetric in the column convention; reason: Duplicate labels retain their original probability; reversibility with uniform measure is exactly matrix symmetry.
--   - encoding: second eigenvalue gap and length bound L → mean-zero unit-sphere Rayleigh gap on a nontrivial finite space and a positive natural L; reason: The guards exclude only undefined spectral or zero-denominator cases and hold in the AES application.
--   - encoding: for every permutation used by the reference chain → for each reference label with nonzero probability, a fixed-length PMF of sequences with exact target marginals; reason: Repeated reference labels naming the same permutation impose equivalent existence conditions and do not change any chain.
-- source:
--   Angelos Pelecanos, Stefano Tessaro, Vinod Vaikuntanathan, STOC 2027 submission #1279 (October 2026), Theorem 2.18 and §2.4 preamble, p.13 (PDF p.13)

import Mathlib
import Definitions.Def_AESIndependence_Main_LabelChains

namespace AESIndependence.Main
open scoped BigOperators Classical

theorem balanced_comparison {X R T : Type} [Fintype X] [Nontrivial X]
    (Kref : LabelChain X R) (Ktar : LabelChain X T)
    (href : IsReversibleUniform Kref.matrix) (htar : IsReversibleUniform Ktar.matrix)
    (L : ℕ) (hL : 0 < L)
    (hsim : ∀ v, Kref.law v ≠ 0 → ∃ ℓ : ℕ, ℓ ≤ L ∧
      BalancedSimulation (fun w => (Ktar.action w : X → X)) Ktar.law ℓ (Kref.action v)) :
    spectralGap Kref.matrix / (L : ℝ)^2 ≤ spectralGap Ktar.matrix := by sorry

end AESIndependence.Main
