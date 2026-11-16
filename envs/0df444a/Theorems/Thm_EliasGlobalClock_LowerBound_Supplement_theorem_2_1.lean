-- Prove2me | Theorems.Thm_EliasGlobalClock_LowerBound_Supplement_theorem_2_1
-- name    : EliasGlobalClock.LowerBound.Supplement.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:35:20.380082+00:00
-- url     : https://prove2.me/theorems/bb5d22ee-2e89-4eb6-9292-cb5c192b3f01
-- title:
--   Theorem 2.1 — MonoElias: Elias lengths, prefix property and aligned 2P monotonicity
-- statement:
--   Let $\mathrm{MonoElias}:\mathbb Z_+\to\{0,1\}^*$ be the code of Appendix A.1: $\mathrm{MonoElias}(1)=0$ and $\mathrm{MonoElias}(N)=\mathrm{RBin}(N_k)\|\cdots\|\mathrm{RBin}(N_1)\|0$, where $N_1=N$, $N_i=\lfloor\log_2N_{i-1}\rfloor$, $N_k\in\{2,3\}$, and $\mathrm{RBin}$ reverses all bits of $\mathrm{Bin}$ but the leading $1$. Let $\mathrm{Int}$ be defined with respect to this code. Then:
--
--   1. MonoElias is prefix-free;
--   2. **Length.** $|\mathrm{MonoElias}(N)|=|\mathrm{Elias}(N)|$ for every $N\ge1$;
--   3. **Prefix.** $\mathrm{Int}(t)\ge1$ for every $t\ge1$;
--   4. **Monotonicity.** For every $N\ge1$, with $P=2^{|\mathrm{MonoElias}(N)|}$, and every $j\ge0$, the sequence $(\mathrm{Int}(t))_{t\in J\cap\mathbb Z_+}$ over
--   $$J=[\,j(2P),\,(j+1)(2P)\,)$$
--   contains $1,2,\dots,N$ as a subsequence.
--
--   MonoElias is the explicit code used in the second clause of Theorem 3.1; monotonicity guarantees that every target $1,\dots,N$ is visited in order in every short aligned interval of global time.
--
--   Differences from the source:
--   - generalization: there exists a prefix-free code MonoElias with the stated properties → the concrete code MonoElias constructed in Appendix A.1 has all the stated properties; reason: the source names and constructs this code and proves the properties for it; the Lean statement implies the existential
--   - encoding: Int(t) is the unique N whose codeword is a prefix of Bin_lsb(t)∥0^∞, or 0 → decode returns the unique positive N with that property, and 0 if none (or if not unique); reason: for a prefix-free code at most one codeword is a prefix of an infinite string, so the two agree
--   - encoding: (Int(t))_{t∈J} contains 1, 2, …, N as a subsequence → there are strictly increasing positive times τ_1<⋯<τ_N in J with Int(τ_i)=i; reason: definition of a subsequence; the sequence Int is indexed by positive times
-- source:
--   Kuowen Chen, Shengquan Du, Tsvi Kopelowitz, Seth Pettie, Ben Plosk, STOC 2027 submission #1311 (October 2026), The Necessity of Elias Codes in the Global Clock Model, printed p.6 / PDF p.7, Theorem 2.1; restated and proved printed p.22 / PDF p.23, Appendix A.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1311.pdf

import Definitions.Def_EliasGlobalClock_LowerBound_Supplement_codes

namespace EliasGlobalClock.LowerBound.Supplement

/-- Theorem 2.1 (printed p.6 / PDF p.7; restated and proved printed p.22 / PDF p.23).
The concrete code MonoElias of Appendix A.1 is prefix-free, has exactly the Elias ω-code
lengths, every positive `t` decodes to some `Int(t) ≥ 1`, and every aligned interval
`[j(2P), (j+1)(2P))`, `P = 2^{|MonoElias(N)|}`, contains `1, …, N` as a subsequence of
`(Int(t))_{t ∈ J ∩ ℤ₊}`. -/
theorem theorem_2_1 :
    IsPrefixFree monoElias ∧
    (∀ N : ℕ+, (monoElias N).length = (elias N).length) ∧
    HasPrefixProperty monoElias ∧
    HasMonotonicity monoElias := by sorry

end EliasGlobalClock.LowerBound.Supplement
