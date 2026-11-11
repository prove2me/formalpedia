-- Prove2me | Theorems.Thm_AggregatedCodeTesting_Testing_theorem_6
-- name    : AggregatedCodeTesting.Testing.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:09:08.731201+00:00
-- url     : https://prove2.me/theorems/e9b4aefa-5fa3-436e-95bd-2767b3ba5d5d
-- title:
--   Theorem 6 — a moment test with $\lceil 4\,\mathrm{Bell}(2s)\,w^s/\varepsilon\rceil$ samples for every distinct pair
-- statement:
--   Let $C\le\mathbb F_2^m$ be a binary linear code without identically zero coordinates, $w\ge1$, and let $\ell,\ell'$ be offset sequences of width $w$ with distinct profiles. Then $s=s(\ell,\ell')$ is finite, and there is a multi-index $r$ with $|r|=s$ such that for every $\varepsilon>0$ the midpoint test of the empirical mean of $\psi_r$ — declare $\ell'$ when $N^{-1}\sum_{i=1}^N\psi_r(H^{(i)})$ lies beyond $(c_\ell(r)+c_{\ell'}(r))/2$ on the side of $c_{\ell'}(r)$ — with
--
--   $$
--   N=\Big\lceil \frac{4\,\mathrm{Bell}(2s)\,w^s}{\varepsilon}\Big\rceil
--   $$
--
--   independent samples has error at most $\varepsilon$ under each hypothesis. Here $\mathrm{Bell}(n)$ is the number of set partitions of an $n$-element set.
--
--   Every distinct pair can therefore be tested with $O(w^{s(\ell,\ell')})$ samples, by a single moment of degree $s$; combined with the testing–Hellinger relation it gives the universal lower bound $H^2(P_\ell,P_{\ell'})\ge w^{-s}/(128\,\mathrm{Bell}(2s))$.
--
--   Differences from the source:
--   - reading: "a moment whose empirical mean distinguishes the laws" → the midpoint threshold test of that empirical mean (the rule of the paper's proof); reason: the statement does not name the decision rule and the proof uses the midpoint of the two known means.
--   - encoding: $4\,\mathrm{Bell}(2s)w^s/\varepsilon$ samples → its ceiling; reason: a number of samples is an integer.
--   - encoding: error target $\varepsilon$ unrestricted → $\varepsilon>0$; reason: the sample count divides by $\varepsilon$, and for $\varepsilon\ge1$ the claim is trivial, so only undefined cases are excluded.
-- source:
--   Jianxin Wang, Zixuan Wang, Chenxu Pang, Chaoen Xiao, Lei Zhang, Zaitian Fu, Conghui Zheng, Yiyang Zou, STOC 2027 submission #1555 (October 2026), Theorem 6, printed p. 6 (PDF p. 7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1555.pdf

import Mathlib
import Definitions.Def_AggregatedCodeTesting_Testing_Orders
import Definitions.Def_AggregatedCodeTesting_Testing_HypothesisTesting

open Finset Classical

namespace AggregatedCodeTesting.Testing

/-- Theorem 6 (A test for every distinct pair), printed p. 6 (PDF p. 7): for a code without
identically zero coordinates and distinct profiles, `s = s(ℓ, ℓ′)` is finite and some moment
`ψ_r` with `|r| = s` gives, for every `ε > 0`, a midpoint empirical-mean test with both errors
at most `ε` using `⌈4 Bell(2s) w^s / ε⌉` independent samples. -/
theorem theorem_6 {m : ℕ} (C : Submodule (ZMod 2) (Word m)) (hC : HasNoZeroCoord C)
    (w : ℕ) (hw : 0 < w) (ℓ ℓ' : Fin w → Word m) (hne : profile C ℓ ≠ profile C ℓ') :
    ∃ s : ℕ, momentOrder C ℓ ℓ' = (s : ℕ∞) ∧
      ∃ r : Fin m → ℕ, absIdx r = s ∧ ∀ ε : ℝ, 0 < ε →
        errorFirst (law C ℓ)
            (momentTest C ℓ ℓ' r ⌈4 * (Nat.bell (2 * s) : ℝ) * (w : ℝ) ^ s / ε⌉₊) ≤ ε ∧
        errorSecond (law C ℓ')
            (momentTest C ℓ ℓ' r ⌈4 * (Nat.bell (2 * s) : ℝ) * (w : ℝ) ^ s / ε⌉₊) ≤ ε := by sorry

end AggregatedCodeTesting.Testing
