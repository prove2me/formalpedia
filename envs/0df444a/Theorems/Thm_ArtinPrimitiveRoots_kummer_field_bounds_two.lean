-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_kummer_field_bounds_two
-- name    : ArtinPrimitiveRoots.kummer_field_bounds_two
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-08T09:01:37.17732+00:00
-- url     : https://prove2.me/theorems/11e87367-8de7-4f76-ae63-0521d89c805b
-- title:
--   Lemma 9.1 for a = 2 (OpenAI) — the field bounds for ℚ(μ_q, 2^{1/q}) hold for every prime q ≥ 5 with an absolute constant
-- statement:
--   There is an absolute constant $B$ such that for every prime $q \ge 5$ and every splitting field $K$ over $\mathbb Q$ of $T^q - 2$ (that is, $K = \mathbb Q(\mu_q, 2^{1/q})$), with $n_q = [K : \mathbb Q]$ and $D_q = |\operatorname{disc} K|$:
--
--   1. $n_q = q(q-1)$;
--   2. $D_q \le q^{q(q-2)}\,(q^q 2^{q-1})^{q-1}$;
--   3. $\log D_q + n_q \le B\, n_q \log(2q)$;
--   4. every rational prime $p \nmid 2q$ is unramified in $K$;
--   5. $\zeta_K$ continues holomorphically to $\{\operatorname{Re} s > 1 - 10^{-6},\ s \ne 1\}$ without zeros.
--
--   This is Lemma 9.1 (`ArtinPrimitiveRoots.kummer_field_bounds`) for $a = 2$, with the threshold $q_0 = 5$ made explicit. The paper asserts it in the proof of Lemma 9.1 and uses it for the case $a = 2$ of Proposition 2.2.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 60, proof of Lemma 9.1: “Fix a rational prime $\ell \mid a$ […] Take $q$ large enough that $q \ne \ell$ and $q > v_\ell(a)$. When $a = 2$, the choice $\ell = 2$ works for every prime $q \ge 5$.” And p. 63, proof of Proposition 2.2: “For $a = 2$, the field bounds hold for every $q \ge 5$ with absolute constants, giving the stated specialization.”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 60, 63, Lemma 9.1 and the proof of Proposition 2.2, case a = 2

import Mathlib
import Definitions.Def_ArtinHecke

namespace ArtinPrimitiveRoots

open NumberField Polynomial

theorem kummer_field_bounds_two :
    ∃ B : ℝ, ∀ q : ℕ, q.Prime → 5 ≤ q →
      ∀ (K : Type) [Field K] [NumberField K] [IsSplittingField ℚ K (X ^ q - C (2 : ℚ))],
        Module.finrank ℚ K = q * (q - 1) ∧
        (|discr K| : ℝ) ≤ (q : ℝ) ^ (q * (q - 2)) * ((q : ℝ) ^ q * (2 : ℝ) ^ (q - 1)) ^ (q - 1) ∧
        Real.log |(discr K : ℝ)| + Module.finrank ℚ K ≤
          B * Module.finrank ℚ K * Real.log (2 * q) ∧
        (∀ p : ℕ, p.Prime → ¬ (p : ℤ) ∣ 2 * q →
          ∀ P : Ideal (𝓞 K), P.IsPrime → (p : 𝓞 K) ∈ P →
            P.ramificationIdx ℤ = 1) ∧
        DedekindZeroFreeRight K (1 - 1 / 10 ^ 6) := by
  sorry

end ArtinPrimitiveRoots
