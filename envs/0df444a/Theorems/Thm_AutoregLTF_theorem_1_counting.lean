-- Prove2me | Theorems.Thm_AutoregLTF_theorem_1_counting
-- name    : AutoregLTF.theorem_1_counting
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:54:25.812506+00:00
-- url     : https://prove2.me/theorems/ca0d4ee2-2ef3-4aea-83c6-e49a0546993d
-- title:
--   Proof of Theorem 1, pp.13–14 — the arithmetic of $m=\max\{1,\lfloor(d-1)/378\rfloor-2\}$: $p\le d-1$, $(m+3)p<p^2<d^2$, $d^2\le1512^2m^2$
-- statement:
--   Let $d\ge1$, $T\ge d^2$ and
--
--   $$m=\max\Big\{1,\Big\lfloor\frac{d-1}{378}\Big\rfloor-2\Big\}\qquad(45),\qquad p=378(m+2).$$
--
--   Then:
--
--   1. if $m\ge2$: $p\le d-1$ and $(m+3)p<p^2<d^2$ (so, with $T\ge d^2$, Lemma 3 applies);
--   2. if $m=1$: $d\le1512$;
--   3. if $m\ge2$: $d\le378(m+3)\le1512m$;
--   4. $d^2\le1512^2m^2$, that is $m^2\ge d^2/1512^2$ (and hence $\ge d^2/3024^2$).
--
--   This is the arithmetic of the proof of Theorem 1 that turns $\mathrm{VCdim}(\mathcal F_{d,T})\ge m^2$ (Lemma 3 for $m\ge2$, (46) for $m=1$) into the constant $3024^2$.
--
--   Differences from the source:
--   - encoding: ⌊(d − 1)/378⌋ − 2 (an integer, possibly negative) → natural-number subtraction (d − 1)/378 − 2, truncated at 0; reason: after max{1, ·} both give the same m
--   - encoding: "Lemma 3 therefore gives VCdim(F_{d,T}) ≥ m²", "VCdim(F_{d,T}) ≥ 1 = m²" and "VCdim(F_{d,T}) ≥ m² ≥ d²/1512² ≥ d²/3024²" → only the arithmetic links (p ≤ d − 1, (m + 3)p < p² < d², d ≤ 1512 or d ≤ 378(m + 3) ≤ 1512m, d² ≤ 1512² m²); reason: the VC-dimension links are AutoregLTF.lemma_3, AutoregLTF.eq_46 and the goal AutoregLTF.theorem_1; d² ≤ T is the hypothesis
-- source:
--   Doron-Arad, Mehalel, Mossel, On the VC Dimension of Autoregressive Linear Threshold Functions, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e), proof of Theorem 1, (45) p.13 and the counting, p.14

import Mathlib
import Definitions.Def_AutoregLTF_block

namespace AutoregLTF

/-- **Proof of Theorem 1, the choice (45) of `m` and the counting**, pp.13–14 (PDF pp.13–14).

I. Doron-Arad, I. Mehalel, E. Mossel, *On the VC Dimension of Autoregressive Linear Threshold
Functions*, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e).

Let `d ≥ 1`, `T ≥ d²` and `m = max{1, ⌊(d − 1)/378⌋ − 2}` (45). Then:
1. if `m ≥ 2`: `p = 378(m + 2) ≤ d − 1` and `(m + 3)p < p² < d²`;
2. if `m = 1`: `d ≤ 1512`;
3. if `m ≥ 2`: `d ≤ 378(m + 3) ≤ 1512 m`;
4. `d² ≤ 1512² m²`, that is `m² ≥ d²/1512²`.

This is the arithmetic that turns Lemma 3 and (46) into the constant `3024²` of Theorem 1.

**Formalization Note.** All quantities are natural numbers. `(d − 1)/378` is `⌊(d − 1)/378⌋`
(`d ≥ 1`). `⌊(d − 1)/378⌋ − 2` is natural subtraction, which truncates at `0`; after `max 1` this
agrees with the integer value of (45). `p m = 378(m + 2)` is (13). -/
theorem theorem_1_counting (d T : ℕ) (hd : 1 ≤ d) (hT : d ^ 2 ≤ T) :
    let m := max 1 ((d - 1) / 378 - 2)
    (2 ≤ m → p m ≤ d - 1 ∧ (m + 3) * p m < p m ^ 2 ∧ p m ^ 2 < d ^ 2) ∧
    (m = 1 → d ≤ 1512) ∧
    (2 ≤ m → d ≤ 378 * (m + 3) ∧ 378 * (m + 3) ≤ 1512 * m) ∧
    d ^ 2 ≤ 1512 ^ 2 * m ^ 2 := by sorry

end AutoregLTF
