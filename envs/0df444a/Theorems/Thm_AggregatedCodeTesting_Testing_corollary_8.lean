-- Prove2me | Theorems.Thm_AggregatedCodeTesting_Testing_corollary_8
-- name    : AggregatedCodeTesting.Testing.corollary_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:08:44.032992+00:00
-- url     : https://prove2.me/theorems/4cbbd6e6-e9ff-450f-8fc5-cd773d1194a4
-- title:
--   Corollary 8 — dense bounded perturbations: $H^2\asymp w^{-s}$ and $N^*\asymp w^{s}$
-- statement:
--   Let $C\le\mathbb F_2^m$ be a binary linear code without identically zero coordinates, and fix $\alpha>0$ and $M$. There are positive constants $c_1,c_2,c_3,c_4$ depending only on $C$, $\alpha$ and $M$ such that for every width $w\ge1$ and every distinct, parity-equivalent pair of offset sequences $\ell,\ell'$ of width $w$ whose every block-coset count is at least $\alpha w$ and whose corresponding counts differ by at most $M$, the order $s=s(\ell,\ell')$ and $N^*(\ell,\ell')$ are finite and
--
--   $$
--   c_1\,w^{-s}\le H^2(P_\ell,P_{\ell'})\le c_2\,w^{-s},\qquad c_3\,w^{s}\le N^*(\ell,\ell')\le c_4\,w^{s}.
--   $$
--
--   This is the "same matching exponent" as in Theorem 7 and the universal lower bound (9), now for dense rather than balanced profiles; it is the bounded-step estimate used along the paths of the proof of Theorem 10.
--
--   Differences from the source:
--   - reading: "the same matching exponent holds" → the two-sided bounds $H^2\asymp_{C,\alpha,M}w^{-s}$ and $N^*\asymp_{C,\alpha,M}w^{s}$ of Theorem 7 and (9); reason: these are the matching distance and sample exponents the corollary refers to.
-- source:
--   Jianxin Wang, Zixuan Wang, Chenxu Pang, Chaoen Xiao, Lei Zhang, Zaitian Fu, Conghui Zheng, Yiyang Zou, STOC 2027 submission #1555 (October 2026), Corollary 8, printed p. 8 (PDF p. 9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1555.pdf

import Mathlib
import Definitions.Def_AggregatedCodeTesting_Testing_Model
import Definitions.Def_AggregatedCodeTesting_Testing_HypothesisTesting
import Definitions.Def_ReplicableDecisions_hellinger

open Finset Classical

namespace AggregatedCodeTesting.Testing

/-- Corollary 8 (Dense bounded perturbations), printed p. 8 (PDF p. 9): for fixed `C` (no
identically zero coordinate), `α > 0` and `M`, the matching exponent of Theorem 7 holds for
distinct, parity-equivalent, `α`-dense profiles whose corresponding block-coset counts differ by
at most `M`: `H² ≍ w^{-s(ℓ,ℓ′)}` and `N* ≍ w^{s(ℓ,ℓ′)}`, constants depending on `C, α, M`. -/
theorem corollary_8 {m : ℕ} (C : Submodule (ZMod 2) (Word m)) (hC : HasNoZeroCoord C)
    (α : ℝ) (hα : 0 < α) (M : ℝ) :
    ∃ c₁ c₂ c₃ c₄ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < c₃ ∧ 0 < c₄ ∧
      ∀ w : ℕ, 0 < w → ∀ ℓ ℓ' : Fin w → Word m,
        profile C ℓ ≠ profile C ℓ' → ParityEquivalent C ℓ ℓ' →
        IsDense C α ℓ → IsDense C α ℓ' →
        (∀ D ∈ blocks C, ∀ x : Word m,
          |(cosetCount C D ℓ x : ℝ) - (cosetCount C D ℓ' x : ℝ)| ≤ M) →
        ∃ s N : ℕ, momentOrder C ℓ ℓ' = (s : ℕ∞) ∧
          c₁ / (w : ℝ) ^ s ≤ ReplicableDecisions.hellingerSq (law C ℓ) (law C ℓ') ∧
          ReplicableDecisions.hellingerSq (law C ℓ) (law C ℓ') ≤ c₂ / (w : ℝ) ^ s ∧
          sampleComplexity (law C ℓ) (law C ℓ') = (N : ℕ∞) ∧
          c₃ * (w : ℝ) ^ s ≤ (N : ℝ) ∧ (N : ℝ) ≤ c₄ * (w : ℝ) ^ s := by sorry

end AggregatedCodeTesting.Testing
