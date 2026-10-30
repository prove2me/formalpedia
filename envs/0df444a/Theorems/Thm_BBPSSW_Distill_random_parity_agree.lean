-- Prove2me | Theorems.Thm_BBPSSW_Distill_random_parity_agree
-- name    : BBPSSW.Distill.random_parity_agree
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:15:56.385094+00:00
-- url     : https://prove2.me/theorems/fcb4236c-0245-4aff-a4c1-f2a292efb6e1
-- title:
--   Random subset parities: two distinct strings agree on $r$ parities with probability $\le2^{-r}$
-- statement:
--   Let $x\neq y$ be $n$-bit strings, and choose subsets $S_1,\dots,S_r\subseteq\{1,\dots,n\}$ independently and uniformly at random. Then
--
--   $$\Pr\Big[\textstyle\sum_{i\in S_j}x_i\equiv\sum_{i\in S_j}y_i\pmod 2\ \text{ for all }j\Big]\le2^{-r}.$$
--
--   This is the fact behind BXOR tests: each test reveals the parity of a random subset of the unknown error string, so about $\log_2$ (number of candidates) tests single it out.
--
--   Differences from the source:
--   - encoding: probability over r independent random subsets → the number of agreeing r-tuples of subsets divided by the number (2^n)^r of all r-tuples; reason: uniform independent subsets; bits in ZMod 2
-- source:
--   Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, Purification of Noisy Entanglement and Faithful Teleportation via Noisy Channels, arXiv:quant-ph/9511027v2, p. 3, unnumbered bullet ("For any two distinct n-bit strings …")

import Mathlib

namespace BBPSSW.Distill

/-- **Random subset parities separate distinct strings.**
Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, *Purification of Noisy Entanglement
and Faithful Teleportation via Noisy Channels*, arXiv:quant-ph/9511027v2, p. 3 (unnumbered bullet): "For any two distinct n-bit strings the probability that they
agree on the parities of r independent random subsets of their bits is ≤ 2^−r [10]."

Let `x ≠ y` be `n`-bit strings. Choose `r` subsets `S₁, …, S_r ⊆ {1, …, n}` independently and
uniformly at random (all `(2^n)^r` tuples equally likely). The probability that
`∑_{i ∈ S_j} x_i = ∑_{i ∈ S_j} y_i (mod 2)` for every `j` is at most `2^{−r}`.

**Formalization Note.** Bits are `ZMod 2`; the probability is the number of agreeing tuples
`(S_j)_{j < r}` divided by the number `(2^n)^r` of all tuples. -/
theorem random_parity_agree (n r : ℕ) (x y : Fin n → ZMod 2) (hxy : x ≠ y) :
    ((Finset.univ.filter fun S : Fin r → Finset (Fin n) =>
          ∀ j, ∑ i ∈ S j, x i = ∑ i ∈ S j, y i).card : ℝ) /
        (Fintype.card (Fin r → Finset (Fin n)) : ℝ) ≤ (1 / 2 : ℝ) ^ r := by sorry

end BBPSSW.Distill
