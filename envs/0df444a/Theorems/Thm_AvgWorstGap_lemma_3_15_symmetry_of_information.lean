-- Prove2me | Theorems.Thm_AvgWorstGap_lemma_3_15_symmetry_of_information
-- name    : AvgWorstGap.lemma_3_15_symmetry_of_information
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:51:18.198335+00:00
-- url     : https://prove2.me/theorems/7c5224a1-5e96-4f3f-8def-64fb4c1ad9b9
-- title:
--   Lemma 3.15 — symmetry of information for pKt (cited from [HKLO24, Lemma 36])
-- statement:
--   Let $O$ be any oracle with $\mathrm{Gap}\text{-}\mathrm{MINpKT}^O\in\mathsf{prBPP}$. Then there are polynomials $p_{\mathrm{SoI}}$ and $p_0$ and a threshold $N_0$ such that for all strings $x,y$ with $|x|+|y|\ge N_0$ and every $t\ge p_0(|x|+|y|)$,
--   $$\mathrm{pK}^{p_{\mathrm{SoI}}(t)}(y\mid x)\le\mathrm{pK}^t(x,y)-\mathrm{pK}^{p_{\mathrm{SoI}}(t)}(x)+\log p_{\mathrm{SoI}}(t).$$
--   All three complexities are unrelativized and have $\lambda=2/3$, as printed.
--
--   Under the hypothesis, the complexity of a pair splits, up to polynomial time and logarithmic slack, into the complexity of the first component plus the conditional complexity of the second. The paper cites the result (see, e.g., [HKLO24, Lemma 36]) and uses it in the proof of Lemma 3.14.
--
--   **Formalization Note** The subtracted term is moved to the left-hand side, so the inequality is stated in the extended reals without subtraction.
--
--   Differences from the source:
--   - reading: "for all sufficiently large x, y" → for all x, y with |x| + |y| ≥ N0; reason: the stronger of the two readings (it also covers pairs where one string is short)
--   - encoding: an inequality of the form A ≤ B − C + D → A + C ≤ B + D in EReal; reason: avoids ⊤ − ⊤; equivalent whenever the values are finite
--   - reading: instances (x, 1^s, 1^t, 1^a, 1^b) with any a, b in Defs. 2.9/2.10 → an instance is in YES or NO only if 1 ≤ b ≤ a; reason: b/a and (b−1)/a must lie in [0,1], the domain of Def. 2.2; read literally, (x, 1^0, 1^0, 1^1, 1^0) is in YES ∩ NO (pK^0_0(x) = 0 ≤ 0 and pK^{ρ(1)}_{−1}(x) = 0 ≥ 0 + log 1), so no oracle's problem would be in prBPP
--   - encoding: a constant c > 0 with ρ(n) = n^c → an integer c ≥ 1; reason: ρ is ℕ-valued; a larger c only shrinks NO, so integer c ≥ 1 is equivalent
--   - encoding: multi-tape machines over {0,1,⊥} with a fixed standard encoding (details unspecified) → the concrete Machine (alphabet {0,1,⊥,blank}, one-way infinite tapes, one-step oracle answers) and the concrete encoding code; reason: the paper fixes none of these details
--   - encoding: tuples and pairs of strings → the self-delimiting tupleEnc / pairStr; reason: the paper fixes no encoding
--   - encoding: minima over ℕ, log, comparisons with s + log ρ → values in ℕ∞ (⊤ for an empty minimum), Real.logb 2, comparisons in EReal; reason: Lean convention; same instances
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), Lemma 3.15, p.28

import Mathlib
import Definitions.Def_AvgWorstGap_GapMINpKT

namespace AvgWorstGap

open NKtLB

/-- **Lemma 3.15 (Symmetry of Information for pKt; see, e.g., [HKLO24, Lemma 36])** (cited;
arXiv:2610.19162, version of October 30, 2026, p.28): "Let `O` be any oracle. If `Gap-MINpKT^O ∈ prBPP`, then there exist polynomials
`pSoI` and `p0` such that for all sufficiently large `x, y ∈ {0, 1}∗` and every
`t ≥ p0(|x| + |y|)`, `pK^{pSoI(t)}(y | x) ≤ pK^t(x, y) − pK^{pSoI(t)}(x) + log pSoI(t)`."

**Formalization Note.** "Sufficiently large `x, y`" is `N0 ≤ |x| + |y|`. All three `pK` terms are
unrelativized with `λ = 2/3`, as printed. The pair `(x, y)` is `pairStr x y`. The subtracted term
is moved to the left, so the inequality is stated in `EReal` without subtraction (equivalent when
the values are finite). -/
theorem lemma_3_15_symmetry_of_information (O : Set (List Bool)) (h : GapInPrBPP O) :
    ∃ (pSoI p₀ : Polynomial ℕ) (N₀ : ℕ), ∀ x y : List Bool, N₀ ≤ x.length + y.length →
      ∀ t : ℕ, p₀.eval (x.length + y.length) ≤ t →
        toEReal (pK ∅ (pSoI.eval t) (2 / 3) y x) + toEReal (pK ∅ (pSoI.eval t) (2 / 3) x []) ≤
          toEReal (pK ∅ t (2 / 3) (pairStr x y) []) +
            ((Real.logb 2 ((pSoI.eval t : ℕ) : ℝ) : ℝ) : EReal) := by sorry

end AvgWorstGap
