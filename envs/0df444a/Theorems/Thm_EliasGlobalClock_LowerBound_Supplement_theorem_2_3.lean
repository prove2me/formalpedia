-- Prove2me | Theorems.Thm_EliasGlobalClock_LowerBound_Supplement_theorem_2_3
-- name    : EliasGlobalClock.LowerBound.Supplement.theorem_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:36:24.4253+00:00
-- url     : https://prove2.me/theorems/3c0a073c-495e-47e0-acce-af9a70cec4ab
-- title:
--   Theorem 2.3 — SmoothCode: length ≤ Elias + 1, prefix property and smooth length increments
-- statement:
--   Let $\mathrm{SmoothCode}:\mathbb Z_+\to\{0,1\}^*$ be the code of Appendix B: $\mathrm{SmoothCode}(1)=00$, $\mathrm{SmoothCode}(2)=01$ and $\mathrm{SmoothCode}(N)=1\|\mathrm{SmoothCode}(\mathrm{gr}(N))\|\mathrm{Enc}(N)$ for $N\ge3$, where $\mathrm{gr}(N)$ is the index of the group $G_r\ni N$ and $\mathrm{Enc}(N)$ is the subgroup bit followed by the padded offset of $N$ in its subgroup. Let $\mathrm{Int}$ be defined with respect to this code. Then:
--
--   1. SmoothCode is prefix-free;
--   2. **Length.** $|\mathrm{SmoothCode}(N)|\le|\mathrm{Elias}(N)|+1$ for every $N\ge1$;
--   3. **Prefix property.** $\mathrm{Int}(t)\ge1$ for every $t\ge1$;
--   4. **Smoothness.** For every $N\ge1$,
--   $$|\mathrm{SmoothCode}(N)|\le|\mathrm{SmoothCode}(N+1)|\le|\mathrm{SmoothCode}(N)|+1,\qquad |\mathrm{SmoothCode}(2N)|\le|\mathrm{SmoothCode}(N)|+2.$$
--
--   SmoothCode schedules the target population sizes of Algorithm 2; smoothness keeps the test period of neighbouring targets within a factor of $2$ and of doubled targets within a factor of $4$.
--
--   Differences from the source:
--   - generalization: there exists a prefix-free code SmoothCode with the stated properties → the concrete code SmoothCode constructed in Appendix B has all the stated properties; reason: the source names and constructs this code and proves the properties for it; the Lean statement implies the existential
--   - encoding: Int(t) is the unique N whose codeword is a prefix of Bin_lsb(t)∥0^∞, or 0 → decode returns the unique positive N with that property, and 0 if none (or if not unique); reason: for a prefix-free code at most one codeword is a prefix of an infinite string, so the two agree
-- source:
--   Kuowen Chen, Shengquan Du, Tsvi Kopelowitz, Seth Pettie, Ben Plosk, STOC 2027 submission #1311 (October 2026), The Necessity of Elias Codes in the Global Clock Model, printed p.7 / PDF p.8, Theorem 2.3; restated and proved printed pp.24–26 / PDF pp.25–27, Appendix B; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1311.pdf

import Definitions.Def_EliasGlobalClock_LowerBound_Supplement_codes

namespace EliasGlobalClock.LowerBound.Supplement

/-- Theorem 2.3 (printed p.7 / PDF p.8; restated and proved printed pp.24–26 / PDF pp.25–27).
The concrete SmoothCode of Appendix B is prefix-free, has length at most `|Elias(N)| + 1`,
has the prefix property, nondecreasing lengths with increments at most `1`, and
`|SmoothCode(2N)| ≤ |SmoothCode(N)| + 2`. -/
theorem theorem_2_3 :
    IsPrefixFree smoothCode ∧
    (∀ N : ℕ+, (smoothCode N).length ≤ (elias N).length + 1) ∧
    HasPrefixProperty smoothCode ∧
    (∀ N : ℕ+, (smoothCode N).length ≤ (smoothCode (N + 1)).length ∧
      (smoothCode (N + 1)).length ≤ (smoothCode N).length + 1) ∧
    (∀ N : ℕ+, (smoothCode (2 * N)).length ≤ (smoothCode N).length + 2) := by sorry

end EliasGlobalClock.LowerBound.Supplement
