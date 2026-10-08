-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_smooth_prime_ideal_estimate
-- name    : ArtinPrimitiveRoots.smooth_prime_ideal_estimate
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-08T09:01:52.465102+00:00
-- url     : https://prove2.me/theorems/c05a3f40-367f-42f3-81b0-d5b4d796d5fb
-- title:
--   Lemma 9.2 (OpenAI) — smooth prime-ideal estimate with error linear in log D + n, given a zero-free region
-- statement:
--   Let $0 < \delta < 1/2$, and let $f : \mathbb R \to \mathbb R$ be smooth and nonnegative, with compact support contained in $(0, \infty)$. There is a constant $C$ such that for every number field $K$ of degree $n$ and absolute discriminant $D$ whose Dedekind zeta function continues holomorphically to $\{\operatorname{Re} s > 1 - \delta,\ s \ne 1\}$ without zeros (`DedekindZeroFreeRight K (1 - δ)`), and every real $x \ge 2$,
--
--   $$\Theta_{K,f}(x) = \sum_{\mathfrak p} \sum_{j \ge 1} (\log \mathrm N\mathfrak p)\, f\!\left(\frac{(\mathrm N\mathfrak p)^j}{x}\right) \ \le\ C\bigl(x + x^{1-\delta}(\log D + n)\bigr),$$
--
--   where $\mathfrak p$ runs over the nonzero prime ideals of $\mathcal O_K$. The constant $C$ depends on $\delta$ and $f$ only, not on $K$ or $x$. Only finitely many terms of the double sum are nonzero, because $f$ has compact support in $(0, \infty)$, and the sum is written as a double `tsum`.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 61: “Lemma 9.2. Fix $0 < \delta < 1/2$ and a nonnegative function $f \in C_c^\infty((0, \infty))$. Let $K$ be a number field of degree $n$ and absolute discriminant $D$ whose Dedekind zeta function has no zero in $\operatorname{Re} s > 1 - \delta$. For every real $x \ge 2$, $\Theta_{K,f}(x) := \sum_{\mathfrak p}\sum_{j \ge 1} (\log \mathrm N\mathfrak p) f\bigl(\frac{(\mathrm N\mathfrak p)^j}{x}\bigr) \ll_f x + x^{1-\delta}(\log D + n)$, (9.5) where $\mathfrak p$ ranges over the nonzero prime ideals of $K$. The implied constant is independent of $K$ and $x$.”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 61, Lemma 9.2

import Mathlib
import Definitions.Def_ArtinHecke

namespace ArtinPrimitiveRoots

open NumberField

theorem smooth_prime_ideal_estimate (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) (f : ℝ → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) (hfs : tsupport f ⊆ Set.Ioi 0)
    (hf0 : ∀ t, 0 ≤ f t) :
    ∃ C : ℝ, ∀ (K : Type) [Field K] [NumberField K], DedekindZeroFreeRight K (1 - δ) →
      ∀ x : ℝ, 2 ≤ x →
        ∑' P : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥}, ∑' j : ℕ,
            Real.log (Ideal.absNorm P.1) * f ((Ideal.absNorm P.1 : ℝ) ^ (j + 1) / x) ≤
          C * (x + x ^ (1 - δ) * (Real.log |(discr K : ℝ)| + Module.finrank ℚ K)) := by
  sorry

end ArtinPrimitiveRoots
