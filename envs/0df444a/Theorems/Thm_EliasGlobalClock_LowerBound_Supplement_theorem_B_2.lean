-- Prove2me | Theorems.Thm_EliasGlobalClock_LowerBound_Supplement_theorem_B_2
-- name    : EliasGlobalClock.LowerBound.Supplement.theorem_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:42:58.537205+00:00
-- url     : https://prove2.me/theorems/a4d135a0-5f2a-4d5b-8695-948bea6f9bc3
-- title:
--   Theorem B.2 — SmoothMonoCode: smooth, Elias-length and aligned 2P monotone
-- statement:
--   Let $\mathrm{SmoothMonoCode}:\mathbb Z_+\to\{0,1\}^*$ be the code of Appendix B.0.1, obtained from $\mathrm{SmoothCode}_{\mathrm{lsb}}$ by reassigning the codewords inside each $H_r=\{2^r+1,\dots,2^{r+1}\}$ with $d_r=d_{r+1}$, and let $\mathrm{Int}$ be defined with respect to it. Then:
--
--   1. SmoothMonoCode is prefix-free;
--   2. **Length.** $|\mathrm{SmoothMonoCode}(N)|\le|\mathrm{Elias}(N)|+1$ for every $N\ge1$;
--   3. **Prefix property.** $\mathrm{Int}(t)\ge1$ for every $t\ge1$;
--   4. **Smoothness.** $|\mathrm{SmoothMonoCode}(N+1)|\le|\mathrm{SmoothMonoCode}(N)|+1$ and $|\mathrm{SmoothMonoCode}(2N)|\le|\mathrm{SmoothMonoCode}(N)|+2$ for every $N\ge1$;
--   5. **Monotonicity.** For every $N\ge1$, with $P=2^{|\mathrm{SmoothMonoCode}(N)|}$, and every aligned interval $J=[\,j(2P),(j+1)(2P)\,)$, the sequence $(\mathrm{Int}(x))$ over positive $x\in J$ contains $1,\dots,N$ as a subsequence.
--
--   This combines the smoothness of SmoothCode with the monotonicity of MonoElias at the same $2P$ window, which the unshuffled code $\mathrm{SmoothCode}_{\mathrm{lsb}}$ only achieves at $4P$ (Lemma B.1).
--
--   Differences from the source:
--   - generalization: there exists a prefix-free code SmoothMonoCode with the stated properties → the concrete code SmoothMonoCode constructed in Appendix B.0.1 has all the stated properties; reason: the source names and constructs this code and proves the properties for it; the Lean statement implies the existential
--   - encoding: Int(t) is the unique N whose codeword is a prefix of Bin_lsb(t)∥0^∞, or 0 → decode returns the unique positive N with that property, and 0 if none (or if not unique); reason: for a prefix-free code at most one codeword is a prefix of an infinite string, so the two agree
--   - encoding: (Int(t))_{t∈J} contains 1, 2, …, N as a subsequence → there are strictly increasing positive times τ_1<⋯<τ_N in J with Int(τ_i)=i; reason: definition of a subsequence; the sequence Int is indexed by positive times
-- source:
--   Kuowen Chen, Shengquan Du, Tsvi Kopelowitz, Seth Pettie, Ben Plosk, STOC 2027 submission #1311 (October 2026), The Necessity of Elias Codes in the Global Clock Model, printed p.28 / PDF p.29, Theorem B.2; construction and proof printed pp.26–28 / PDF pp.27–29, Appendix B.0.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1311.pdf

import Definitions.Def_EliasGlobalClock_LowerBound_Supplement_codes

namespace EliasGlobalClock.LowerBound.Supplement

/-- Theorem B.2 (printed p.28 / PDF p.29). The concrete SmoothMonoCode of Appendix B.0.1 is
prefix-free, has length at most `|Elias(N)| + 1`, the prefix property, both smoothness upper
bounds, and the aligned `2P` monotonicity with `P = 2^{|SmoothMonoCode(N)|}`. -/
theorem theorem_B_2 :
    IsPrefixFree smoothMonoCode ∧
    (∀ N : ℕ+, (smoothMonoCode N).length ≤ (elias N).length + 1) ∧
    HasPrefixProperty smoothMonoCode ∧
    (∀ N : ℕ+, (smoothMonoCode (N + 1)).length ≤ (smoothMonoCode N).length + 1) ∧
    (∀ N : ℕ+, (smoothMonoCode (2 * N)).length ≤ (smoothMonoCode N).length + 2) ∧
    HasMonotonicity smoothMonoCode := by sorry

end EliasGlobalClock.LowerBound.Supplement
