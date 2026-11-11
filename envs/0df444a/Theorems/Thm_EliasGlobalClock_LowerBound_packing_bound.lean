-- Prove2me | Theorems.Thm_EliasGlobalClock_LowerBound_packing_bound
-- name    : EliasGlobalClock.LowerBound.packing_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:05:38.654431+00:00
-- url     : https://prove2.me/theorems/5771310f-b256-4909-9f00-fc0a5be00a09
-- title:
--   Lemma 4.4 — uniform summable packing with an explicit constant
-- statement:
--   Fix $0<\eta<1$, put $m_i=2\lceil(2^i)^{\eta/2}\rceil$ for $i\ge1$, and let $\ell_i$ be arbitrary positive nondecreasing integer window lengths. There is a positive finite constant $C$, chosen before the profiles and windows, such that for every nonnegative nondecreasing profile $s$,
--
--   $$\sum_{i=1}^{\infty}\frac1{\ell_i}\sum_{j=1}^{\ell_i}K(m_i s(j))\le C,
--   \qquad C\le\frac{2\sqrt2}{1-2^{-\eta/4}}.$$
--
--   The series is explicitly required to be summable. In the source, $s(j)=s_{t\mid Y}(j)$; the bound is uniform over every slot, shared input and protocol. No feasibility restriction $m_i\ell_i\le2^i$ is imposed. The paper states an unspecified finite $C_\eta$; its proof yields the displayed constant.
--
--   Differences from the source:
--   - generalization: contention profiles s_{t|Y} from a protocol and nondecreasing latency windows ℓᵢ=L(nᵢ,ϵᵢ) → every nonnegative nondecreasing real profile s and every positive nondecreasing integer window sequence ℓ; reason: the source proof uses only nonnegativity and monotonicity of the profile and positivity and monotonicity of the windows; each admissible source profile and window sequence is included
--   - generalization: there exists a finite uniform constant Cη → there exists a positive uniform C no greater than 2√2/(1−2^(−η/4)); reason: the proof bounds each of its two geometric tails by 1/(1−2^(−η/4)) and incurs at most √2 from rounding
--   - encoding: an infinite nonnegative series bounded by Cη → Summable together with the same bound on the real tsum, after shifting index i=k+1; reason: summability prevents Lean’s default real tsum on a divergent series from satisfying the inequality
-- source:
--   Kuowen Chen, Shengquan Du, Tsvi Kopelowitz, Seth Pettie, Ben Plosk, STOC 2027 submission #1311 (October 2026), printed p.12, PDF p.13, Lemma 4.4 and its proof; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1311.pdf

import Definitions.Def_EliasGlobalClock_LowerBound_contentionModel

open scoped BigOperators

namespace EliasGlobalClock.LowerBound

/-- Lemma 4.4, printed p.12 / PDF p.13. Stated for every nonnegative
nondecreasing profile, which includes s_{t|Y}. The proof's two geometric tails
give 2 sqrt(2)/(1-2^(-η/4)). No population feasibility assumption is imposed. -/
theorem packing_bound (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ C : ℝ, 0 < C ∧ C ≤ packingConstant η ∧
      ∀ (s : ℕ → ℝ) (ℓ : ℕ+ → ℕ),
        (∀ j, 0 ≤ s j) → Monotone s → (∀ i, 0 < ℓ i) → Monotone ℓ →
        Summable (fun k : ℕ => packingTerm η s ℓ ⟨k + 1, Nat.succ_pos k⟩) ∧
        (∑' k : ℕ, packingTerm η s ℓ ⟨k + 1, Nat.succ_pos k⟩) ≤ C := by sorry

end EliasGlobalClock.LowerBound
