-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_kummer_field_bounds
-- name    : ArtinPrimitiveRoots.kummer_field_bounds
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-08T09:01:50.877763+00:00
-- url     : https://prove2.me/theorems/2edb1a9d-6498-4f64-8db2-aa8f54a0d74d
-- title:
--   Lemma 9.1 (OpenAI) — degree and discriminant of ℚ(μ_q, a^{1/q}), unramified primes, and a zero-free region for its Dedekind zeta function
-- statement:
--   Let $a$ be an integer with $|a| > 1$. There are $q_0$ and $B$ such that for every prime $q \ge q_0$ and every splitting field $K$ over $\mathbb Q$ of $T^q - a$ (that is, $K = K_q = \mathbb Q(\mu_q, a^{1/q})$), with $n_q = [K : \mathbb Q]$ and $D_q = |\operatorname{disc} K|$:
--
--   1. $n_q = q(q-1)$;
--   2. $D_q \le q^{q(q-2)}\,(q^q |a|^{q-1})^{q-1}$;
--   3. $\log D_q + n_q \le B\, n_q \log(2q)$;
--   4. every rational prime $p \nmid aq$ is unramified in $K$: every prime ideal of $\mathcal O_K$ containing $p$ has ramification index $1$ over $\mathbb Z$;
--   5. the Dedekind zeta function $\zeta_K$ continues holomorphically to $\{\operatorname{Re} s > 1 - 10^{-6},\ s \ne 1\}$ without zeros (`DedekindZeroFreeRight K (1 - 1/10^6)`).
--
--   $q_0$ and $B$ depend only on $a$. The bound $\ll_a$ of the paper is written with the explicit constant $B$.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 60: “Lemma 9.1. Fix an integer $a$ with $|a| > 1$. For every sufficiently large prime $q$, the degree $n_q = [K_q : \mathbb Q]$ and absolute discriminant $D_q$ satisfy $n_q = q(q-1)$, $D_q \le q^{q(q-2)}(q^q|a|^{q-1})^{q-1}$, $\log D_q + n_q \ll_a n_q \log(2q)$. (9.1) Every rational prime $p \nmid aq$ is unramified in $K_q$, and $\zeta_{K_q}(s) \ne 0$ $(\operatorname{Re} s > 1 - \delta_0,\ s \ne 1)$. (9.2)” Here $\delta_0 = 10^{-6}$. The zero-free region comes from Theorem 1.2 (`ArtinPrimitiveRoots.hecke_zero_free`), applied over $\mathbb Q(\mu_{12q})$, through abelian Artin factorization.
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 60, Lemma 9.1

import Mathlib
import Definitions.Def_ArtinHecke

namespace ArtinPrimitiveRoots

open NumberField Polynomial

theorem kummer_field_bounds (a : ℤ) (ha : 1 < |a|) :
    ∃ q₀ : ℕ, ∃ B : ℝ, ∀ q : ℕ, q.Prime → q₀ ≤ q →
      ∀ (K : Type) [Field K] [NumberField K] [IsSplittingField ℚ K (X ^ q - C (a : ℚ))],
        Module.finrank ℚ K = q * (q - 1) ∧
        (|discr K| : ℝ) ≤ (q : ℝ) ^ (q * (q - 2)) * ((q : ℝ) ^ q * (|a| : ℝ) ^ (q - 1)) ^ (q - 1) ∧
        Real.log |(discr K : ℝ)| + Module.finrank ℚ K ≤
          B * Module.finrank ℚ K * Real.log (2 * q) ∧
        (∀ p : ℕ, p.Prime → ¬ (p : ℤ) ∣ a * q →
          ∀ P : Ideal (𝓞 K), P.IsPrime → (p : 𝓞 K) ∈ P →
            P.ramificationIdx ℤ = 1) ∧
        DedekindZeroFreeRight K (1 - 1 / 10 ^ 6) := by
  sorry

end ArtinPrimitiveRoots
