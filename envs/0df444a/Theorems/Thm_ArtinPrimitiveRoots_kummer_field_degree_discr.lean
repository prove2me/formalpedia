-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_kummer_field_degree_discr
-- name    : ArtinPrimitiveRoots.kummer_field_degree_discr
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T09:11:44.343977+00:00
-- url     : https://prove2.me/theorems/73fa7c49-46f8-4185-9bd9-75bed7253dda
-- title:
--   Proof of Lemma 9.1 (OpenAI) — degree q(q−1), discriminant bound and unramified primes for ℚ(μ_q, a^{1/q})
-- statement:
--   Let $a \ne 0$ be an integer, let $\ell$ be a prime dividing $a$, and let $q \ne \ell$ be a prime with $q > v_\ell(a)$ (`padicValInt ℓ a < q`). Let $K$ be a splitting field over $\mathbb Q$ of $T^q - a$, that is, $K = K_q = \mathbb Q(\mu_q, a^{1/q})$. Then:
--
--   1. $[K : \mathbb Q] = q(q-1)$;
--   2. $|\operatorname{disc} K| \le q^{q(q-2)}\,(q^q |a|^{q-1})^{q-1}$;
--   3. every rational prime $p \nmid aq$ is unramified in $K$: every prime ideal of $\mathcal O_K$ containing $p$ has ramification index $1$ over $\mathbb Z$.
--
--   These are the algebraic conclusions of Lemma 9.1 (`ArtinPrimitiveRoots.kummer_field_bounds`), under the hypotheses its proof actually uses. They hold for every $q \ge 5$ when $a = 2$ (take $\ell = 2$). The remaining conclusions of Lemma 9.1 are the estimate $\log D_q + n_q \ll_a n_q \log(2q)$, which follows from item 2, and the zero-free region (`ArtinPrimitiveRoots.kummer_zero_free_of_hecke`).
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), pp. 60–61, proof of Lemma 9.1: “Fix a rational prime $\ell \mid a$, and let $v_\ell(a) > 0$ be its valuation. Take $q$ large enough that $q \ne \ell$ and $q > v_\ell(a)$. When $a = 2$, the choice $\ell = 2$ works for every prime $q \ge 5$. The cyclotomic discriminant formula gives $|d_{E_q}| = q^{q-2}$, so $\ell$ is unramified in $E_q$ and the valuation of $a$ at every prime above $\ell$ is $v_\ell(a)$. This is not divisible by $q$, and therefore $a$ is not a $q$th power in $E_q$. […] This proves the degree formula. […] The discriminant tower formula now gives $D_q = |d_{E_q}|^q \mathrm N_{E_q/\mathbb Q}(\mathfrak d_{K_q/E_q}) \le q^{q(q-2)}(q^q|a|^{q-1})^{q-1}$. This also proves unramifiedness away from $aq$, […]”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 60–61, proof of Lemma 9.1 (degree, discriminant, ramification)

import Mathlib

namespace ArtinPrimitiveRoots

open NumberField Polynomial

theorem kummer_field_degree_discr (a : ℤ) (ℓ q : ℕ) (hℓ : ℓ.Prime) (hℓa : (ℓ : ℤ) ∣ a)
    (ha : a ≠ 0) (hq : q.Prime) (hqℓ : q ≠ ℓ) (hqv : padicValInt ℓ a < q)
    (K : Type) [Field K] [NumberField K] [IsSplittingField ℚ K (X ^ q - C (a : ℚ))] :
    Module.finrank ℚ K = q * (q - 1) ∧
    (|discr K| : ℝ) ≤ (q : ℝ) ^ (q * (q - 2)) * ((q : ℝ) ^ q * (|a| : ℝ) ^ (q - 1)) ^ (q - 1) ∧
    (∀ p : ℕ, p.Prime → ¬ (p : ℤ) ∣ a * q →
      ∀ P : Ideal (𝓞 K), P.IsPrime → (p : 𝓞 K) ∈ P → P.ramificationIdx ℤ = 1) := by
  sorry

end ArtinPrimitiveRoots
