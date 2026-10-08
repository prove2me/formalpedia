-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_kummer_zero_free_of_hecke
-- name    : ArtinPrimitiveRoots.kummer_zero_free_of_hecke
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-08T09:12:29.449282+00:00
-- url     : https://prove2.me/theorems/c1f4ed70-78b7-4c71-82d2-af9d82962dd5
-- title:
--   Proof of Lemma 9.1 (OpenAI) — zero-free Hecke L-functions over ℚ(μ_{12q}) give a zero-free Dedekind zeta function for ℚ(μ_q, a^{1/q})
-- statement:
--   Let $a \ne 0$ be an integer, $q$ a prime and $\sigma > 0$. Let $F = \mathbb Q(\mu_{12q})$, a number field generated over $\mathbb Q$ by the $12q$-th roots of unity (`IsCyclotomicExtension {12 * q} ℚ F`). Let $K$ be a splitting field over $\mathbb Q$ of $T^q - a$, that is, $K = \mathbb Q(\mu_q, a^{1/q})$. Suppose that for every nonzero ideal $\mathfrak m$ of $\mathcal O_F$, every finite-order Hecke character $\chi$ of $F$ of modulus $\mathfrak m$ has $L(s, \chi)$ zero-free to the right of $\sigma$ (`χ.ZeroFreeRight σ`). Then the Dedekind zeta function $\zeta_K$ continues holomorphically to $\{\operatorname{Re} s > \sigma,\ s \ne 1\}$ without zeros (`DedekindZeroFreeRight K σ`).
--
--   With $\sigma = 1 - 10^{-6}$ the hypothesis is Theorem 1.2 (`ArtinPrimitiveRoots.hecke_zero_free`), since $F$ is cyclotomic and contains $\mu_{12}$, and the conclusion is the zero-free conclusion (9.2) of Lemma 9.1 (`ArtinPrimitiveRoots.kummer_field_bounds`). The hypothesis $\sigma > 0$ keeps the statement to the half-plane in which the paper's primitive $L_F(s, \eta)$ and the series `HeckeChar.LSeries` of the definitions bundle have the same zeros.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 61, proof of Lemma 9.1: “To obtain (9.2), put $F_q = \mathbb Q(\mu_{12q})$, $\widetilde K_q = K_q F_q$. The extension $\widetilde K_q/F_q$ is cyclic, since it is obtained by adjoining $a^{1/q}$ to a field containing $\mu_q$. The extension $\widetilde K_q/K_q$ is also abelian […] Abelian Artin factorization, with one-dimensional Artin functions identified with primitive Hecke functions, gives (9.3), (9.4). […] Every factor in (9.3) is covered by Theorem 1.2, because $F_q$ is cyclotomic and contains $\mu_{12}$. Thus $\zeta_{\widetilde K_q}$ is zero-free in the indicated half-plane. Every factor in (9.4) is an entire nonprincipal Hecke $L$-function. A zero of $\zeta_{K_q}$ there would therefore be a zero of $\zeta_{\widetilde K_q}$. This proves (9.2).” The factorizations (9.3) and (9.4) are cited from Neukirch, *Algebraic Number Theory*, Chapter VII, Corollary (10.5) and Theorem (10.6).
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 61, proof of Lemma 9.1 (descent of the zero-free region, (9.2)–(9.4))

import Mathlib
import Definitions.Def_ArtinHecke

namespace ArtinPrimitiveRoots

open NumberField Polynomial

theorem kummer_zero_free_of_hecke (a : ℤ) (ha : a ≠ 0) (q : ℕ) (hq : q.Prime) (σ : ℝ)
    (hσ : 0 < σ) (F : Type) [Field F] [NumberField F] [IsCyclotomicExtension {12 * q} ℚ F]
    (hF : ∀ (𝔪 : Ideal (𝓞 F)), 𝔪 ≠ ⊥ → ∀ χ : HeckeChar F 𝔪, χ.ZeroFreeRight σ)
    (K : Type) [Field K] [NumberField K] [IsSplittingField ℚ K (X ^ q - C (a : ℚ))] :
    DedekindZeroFreeRight K σ := by
  sorry

end ArtinPrimitiveRoots
