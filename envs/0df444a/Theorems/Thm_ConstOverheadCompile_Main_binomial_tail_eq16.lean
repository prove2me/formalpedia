-- Prove2me | Theorems.Thm_ConstOverheadCompile_Main_binomial_tail_eq16
-- name    : ConstOverheadCompile.Main.binomial_tail_eq16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:58:17.573829+00:00
-- url     : https://prove2.me/theorems/c0370eee-ad1e-4551-8568-cf8691bf075e
-- title:
--   §2, Eq. (16), second inequality: $\Pr[\mathrm{Bin}(m,1/2)<G]\le e^{-m/8}$ for every integer $m\ge4G$
-- statement:
--   For all nonnegative integers $G$ and $m$ with $m\ge 4G$,
--   $$\Pr[\mathrm{Bin}(m,1/2)<G]=\frac{1}{2^m}\sum_{k=0}^{G-1}\binom{m}{k}\ \le\ e^{-m/8}.$$
--
--   In the paper this bound controls the number of state-injection calls of Algorithm 1: if more than $m$ injections occur, fewer than $G$ of the first $m$ independent fair coins came up "no correction needed". It fixes the cutoff $t_{\max}$ in the proofs of Theorems 2, 7 and 9.
--
--   Differences from the source:
--   - reading: Eq. (16) chains $\Pr[I>m]\le\Pr[\mathrm{Bin}(m,1/2)<G]\le e^{-m/8}$ → only the second inequality; reason: the first concerns the random number $I$ of injection calls of Algorithm 1, an object of the proof of Theorem 9 that this mission does not define; the title marks the part stated.
--   - encoding: $\Pr[\mathrm{Bin}(m,1/2)<G]$ → the explicit sum $2^{-m}\sum_{k<G}\binom mk$; reason: the same number.
-- source:
--   Chenyi Zhang, Xinyu Tan, Robin Kothari, David Gosset, Craig Gidney, Quantum circuit compilation with constant overhead, STOC 2027 submission #397 (October 2026), source.pdf SHA-256 b848604016de1821f5f693c59f328e0b2a9e535bca0b37bb664e6f40dbe3681f, p.7, §2, Eq. (16) (second inequality)

import Mathlib

namespace ConstOverheadCompile.Main

/-- §2, p.7, Eq. (16), second inequality: for all integers `m ≥ 4G ≥ 0`,
`Pr[Bin(m, 1/2) < G] = 2^{-m} Σ_{k < G} C(m, k) ≤ e^{-m/8}`. -/
theorem binomial_tail_eq16 (G m : ℕ) (h : 4 * G ≤ m) :
    (∑ k ∈ Finset.range G, (m.choose k : ℝ)) / 2 ^ m ≤ Real.exp (-(m : ℝ) / 8) := by sorry

end ConstOverheadCompile.Main
