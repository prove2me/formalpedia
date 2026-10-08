-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_mertens_prime_reciprocals
-- name    : ArtinPrimitiveRoots.mertens_prime_reciprocals
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T09:27:01.858996+00:00
-- url     : https://prove2.me/theorems/4d30bcc4-4fed-4f27-8016-77311a1cb137
-- title:
--   Mertens' theorem on prime reciprocals over x^α < p ≤ x^β
-- statement:
--   For reals $0 < \alpha < \beta$, as the real $x \to \infty$,
--
--   $$\sum_{x^\alpha < p \le x^\beta} \frac1p \to \log\frac{\beta}{\alpha},$$
--
--   the sum running over primes $p$.
--
--   This is a classical result that Mathlib lacks; the paper uses it in the proof of Lemma 11.2 and in the proof of Lemma 12.4.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 73: “For fixed $0 < \alpha < \beta$, Mertens' theorem gives $\sum_{x^\alpha < p \le x^\beta}\frac1p \longrightarrow \log(\beta/\alpha)$.”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 73, Mertens' theorem on prime reciprocals, as used on p. 73

import Mathlib

namespace ArtinPrimitiveRoots

open Real Filter Topology

theorem mertens_prime_reciprocals (α β : ℝ) (hα : 0 < α) (hαβ : α < β) :
    Tendsto (fun x : ℝ => ∑ p ∈ (Finset.range (⌊x ^ β⌋₊ + 1)).filter
        (fun p : ℕ => p.Prime ∧ x ^ α < p), (1 : ℝ) / p) atTop (𝓝 (log (β / α))) := by
  sorry

end ArtinPrimitiveRoots
