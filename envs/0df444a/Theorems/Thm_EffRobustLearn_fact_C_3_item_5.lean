-- Prove2me | Theorems.Thm_EffRobustLearn_fact_C_3_item_5
-- name    : EffRobustLearn.fact_C_3_item_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:34:27.593205+00:00
-- url     : https://prove2.me/theorems/b8105dc7-9220-40dd-a3e4-960cda399951
-- title:
--   Fact C.3 item 5 — $\mathrm{VCdim}(\mathrm{Maj}_k(C))\le O(\mathrm{VCdim}(C)k\log(2k))$
-- statement:
--   There is a universal constant $K>0$ such that, for every class $C$ of finite VC dimension and every $k\ge1$, the class $\mathrm{Maj}_k(C)$ has finite VC dimension and
--   $$\mathrm{VCdim}(\mathrm{Maj}_k(C))\le K\,\mathrm{VCdim}(C)\,k\log(2k).$$
--
--   This is what makes the sample size of the main theorem polynomial in $1/\varepsilon$.
--
--   Differences from the source:
--   - reading: every concept class $C$ → $\mathrm{vcDim}\,C<\top$; reason: for infinite VC dimension the right side is $\infty$
--   - reading: $\mathrm{sign}(0)$ unspecified → $\mathrm{sign}(0)=+1$ in $\mathrm{Maj}_k(C)$; reason: the class must be $\pm1$-valued
--   - encoding: $O(\cdot)$ → a universal $K$ fixed before $C$ and $k$; finiteness of the left side stated; reason: toNat would read an infinite value as $0$
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), Fact C.3 item 5, p.41 (PDF p.42), cited from [FS97, Theorem 8]

import Mathlib
import Definitions.Def_UnderstandingML_VC
import Definitions.Def_EffRobustLearn_MajClass

namespace EffRobustLearn

universe u

/-- Fact C.3 item 5, p.41 (arXiv:2609.17655, held version, sha256 312a0857…), cited from [FS97, Theorem 8]: `VCdim(Maj_k(C)) ≤ O(VCdim(C) k log(2k))`, for every class of finite VC dimension and `k ≥ 1`.

**Formalization Note.** The first conjunct says the left side is finite, so that `toNat` is not the junk value of `⊤`. The `O(·)` is a universal `K`, chosen before the class and `k`. -/
theorem fact_C_3_item_5 :
    ∃ K : ℝ, 0 < K ∧
      ∀ (X : Type u) (C : Set (X → Bool)), UnderstandingML.vcDim C < ⊤ → ∀ k : ℕ, 1 ≤ k →
        UnderstandingML.vcDim (MajClass k C) < ⊤ ∧
          ((UnderstandingML.vcDim (MajClass k C)).toNat : ℝ) ≤
            K * (((UnderstandingML.vcDim C).toNat : ℝ) * (k : ℝ) * Real.log (2 * (k : ℝ))) := by sorry

end EffRobustLearn
