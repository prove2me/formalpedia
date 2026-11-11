-- Prove2me | Theorems.Thm_AggregatedCodeTesting_Testing_theorem_7
-- name    : AggregatedCodeTesting.Testing.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:08:27.057829+00:00
-- url     : https://prove2.me/theorems/f0770c49-5494-4a42-b1cb-77ac05a874d6
-- title:
--   Theorem 7 — matching bound $H^2\le c_{C,M}w^{-s}$ and $N^*=\Theta_{C,M}(w^{s})$ for balanced parity-equivalent pairs
-- statement:
--   Let $C\le\mathbb F_2^m$ be a binary linear code without identically zero coordinates and fix $M$. There is a constant $c_{C,M}>0$ such that for every width $w\ge1$ and every distinct, parity-equivalent pair of $M$-balanced offset sequences $\ell,\ell'$ of width $w$, the order $s=s(\ell,\ell')$ is finite and
--
--   $$
--   H^2(P_\ell,P_{\ell'})\le c_{C,M}\,w^{-s(\ell,\ell')}.
--   $$
--
--   Consequently there are constants $c_1,c_2>0$ depending only on $C$ and $M$ such that for all such pairs $N^*(\ell,\ell')$ is finite and
--
--   $$
--   c_1\,w^{s(\ell,\ell')}\le N^*(\ell,\ell')\le c_2\,w^{s(\ell,\ell')}.
--   $$
--
--   Here $H^2(P,Q)=\frac12\sum_h(\sqrt{P(h)}-\sqrt{Q(h)})^2$ and $N^*$ is the least number of samples for which some (possibly randomized) test has both errors at most $1/4$. For bounded count changes the first changed moment degree therefore determines the testing cost exactly.
--
--   Differences from the source:
--   - encoding: $\Theta_{C,M}(w^{s})$ → explicit positive constants $c_1,c_2$ depending only on $C,M$, chosen before $w$ and the profiles; reason: this is the meaning of the asymptotic notation with the stated dependence.
-- source:
--   Jianxin Wang, Zixuan Wang, Chenxu Pang, Chaoen Xiao, Lei Zhang, Zaitian Fu, Conghui Zheng, Yiyang Zou, STOC 2027 submission #1555 (October 2026), Theorem 7, printed p. 7 (PDF p. 8); full proof Appendix A, printed pp. 12–14 (PDF pp. 13–15); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1555.pdf

import Mathlib
import Definitions.Def_AggregatedCodeTesting_Testing_Model
import Definitions.Def_AggregatedCodeTesting_Testing_HypothesisTesting
import Definitions.Def_ReplicableDecisions_hellinger

open Finset Classical

namespace AggregatedCodeTesting.Testing

/-- Theorem 7 (Matching bound), printed p. 7 (PDF p. 8): for fixed `C` (no identically zero
coordinate) and `M`, there is `c_{C,M}` with `H²(P_ℓ, P_{ℓ′}) ≤ c_{C,M} w^{-s(ℓ,ℓ′)}` for every
distinct, parity-equivalent pair of `M`-balanced profiles; consequently
`N*(ℓ, ℓ′) = Θ_{C,M}(w^{s(ℓ,ℓ′)})`. -/
theorem theorem_7 {m : ℕ} (C : Submodule (ZMod 2) (Word m)) (hC : HasNoZeroCoord C) (M : ℝ) :
    (∃ c : ℝ, 0 < c ∧ ∀ w : ℕ, 0 < w → ∀ ℓ ℓ' : Fin w → Word m,
      profile C ℓ ≠ profile C ℓ' → ParityEquivalent C ℓ ℓ' →
      IsBalanced C M ℓ → IsBalanced C M ℓ' →
      ∃ s : ℕ, momentOrder C ℓ ℓ' = (s : ℕ∞) ∧
        ReplicableDecisions.hellingerSq (law C ℓ) (law C ℓ') ≤ c / (w : ℝ) ^ s) ∧
    (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ w : ℕ, 0 < w → ∀ ℓ ℓ' : Fin w → Word m,
      profile C ℓ ≠ profile C ℓ' → ParityEquivalent C ℓ ℓ' →
      IsBalanced C M ℓ → IsBalanced C M ℓ' →
      ∃ s N : ℕ, momentOrder C ℓ ℓ' = (s : ℕ∞) ∧
        sampleComplexity (law C ℓ) (law C ℓ') = (N : ℕ∞) ∧
        c₁ * (w : ℝ) ^ s ≤ (N : ℝ) ∧ (N : ℝ) ≤ c₂ * (w : ℝ) ^ s) := by sorry

end AggregatedCodeTesting.Testing
