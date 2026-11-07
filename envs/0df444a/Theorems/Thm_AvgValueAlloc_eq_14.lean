-- Prove2me | Theorems.Thm_AvgValueAlloc_eq_14
-- name    : AvgValueAlloc.eq_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:37:26.232974+00:00
-- url     : https://prove2.me/theorems/30ff1d22-89e1-42c6-bb79-41658e6944f7
-- title:
--   (13)–(14): $\alpha_{S+T}\le e^{-mk}+e^{-(8k)^{4mk}}$
-- statement:
--   Let $k\ge2$, $T\ge8k$, $S\ge0$ and $m=\lceil1+S/T\rceil$. If the number $d$ of candidates satisfies
--   $$
--   d-1\ \ge\ 4^m(8k)^{8mk},\tag{13}
--   $$
--   then the optimal success of identifying a uniform candidate from $S+T$ independent masks (candidate coordinate $\mathrm{Ber}(k/T)$, the others $\mathrm{Ber}(1/T)$) satisfies
--   $$
--   \alpha_{S+T}\ \le\ e^{-mk}+e^{-(8k)^{4mk}}.\tag{14}
--   $$
--   With Lemma 5.1 this gives the information lower bound $\Omega(\Phi)$.
--
--   Differences from the source:
--   - encoding: candidates I with |I| = d → Fin d; reason: α depends only on d, k, T and the number of masks
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §5.1, p.11, eqs. (13)–(14)

import Mathlib
import Definitions.Def_AvgValueAlloc_alphaId

namespace AvgValueAlloc

/-- **(13)–(14): identification is hard among many candidates.**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §5.1, p.11: "Put m = ⌈1 + S/T⌉. If d − 1 ≥ 4^m(8k)^{8mk}, (13)
then α_{S+T} ≤ e^{−mk} + e^{−(8k)^{4mk}}. (14)" Setting: §5, p.10 (T ≥ 8k, k ≥ 2).

For `k ≥ 2`, `T ≥ 8k`, `S ≥ 0`, `m = ⌈1 + S/T⌉` and `d` candidates with
`d − 1 ≥ 4^m (8k)^{8mk}`: the optimal success of identifying a uniform candidate from `S + T`
independent masks (candidate coordinate `Ber(k/T)`, others `Ber(1/T)`) is at most
`e^{−mk} + e^{−(8k)^{4mk}}`. -/
theorem eq_14 (d k T S : ℕ) (hk : 2 ≤ k) (hT : 8 * k ≤ T)
    (h13 : (4 : ℝ) ^ ⌈(1 : ℝ) + (S : ℝ) / T⌉₊ * (8 * (k : ℝ)) ^ (8 * ⌈(1 : ℝ) + (S : ℝ) / T⌉₊ * k)
      ≤ (d : ℝ) - 1) :
    alphaId d k T (S + T) ≤
      Real.exp (-((⌈(1 : ℝ) + (S : ℝ) / T⌉₊ : ℝ) * k)) +
        Real.exp (-((8 * (k : ℝ)) ^ (4 * ⌈(1 : ℝ) + (S : ℝ) / T⌉₊ * k))) := by sorry

end AvgValueAlloc
