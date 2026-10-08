-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_splitting_test
-- name    : ArtinPrimitiveRoots.splitting_test
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T09:02:43.103901+00:00
-- url     : https://prove2.me/theorems/96a4378a-7942-44d3-9237-df623aa2d407
-- title:
--   Lemma 2.3 (OpenAI) — splitting test: p splits completely in ℚ(μ_q, a^{1/q}) iff p ≡ 1 (mod q) and a^{(p−1)/q} ≡ 1 (mod p)
-- statement:
--   Let $a \ne 0$ be an integer, let $p$ and $q$ be primes with $p \nmid aq$, and let $K$ be a splitting field over $\mathbb Q$ of $T^q - a$, that is, $K = K_q = \mathbb Q(\mu_q, a^{1/q})$. Then $p$ splits completely in $K$ (`SplitsCompletely K p`: $\mathcal O_K$ has $[K : \mathbb Q]$ prime ideals of norm $p$) if and only if
--
--   $$p \equiv 1 \pmod q \quad\text{and}\quad a^{(p-1)/q} \equiv 1 \pmod p.$$
--
--   The second congruence is written in `ZMod p`, with the natural-number quotient $(p-1)/q$ as exponent; it is exact whenever the first congruence holds.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 6: “Lemma 2.3 (Splitting test). Let $a \ne 0$ be an integer, and let $p, q$ be primes with $p \nmid aq$. Then $p$ splits completely in $K_q$ if and only if $p \equiv 1 \pmod q$, $a^{(p-1)/q} \equiv 1 \pmod p$.” Here $K_q = \mathbb Q(\mu_q, a^{1/q})$ (p. 6, (2.3)), and the proof notes that “The field $K_q$ is the splitting field of $T^q - a$.”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 6, Lemma 2.3

import Mathlib
import Definitions.Def_ArtinHecke

namespace ArtinPrimitiveRoots

open NumberField Polynomial

theorem splitting_test (a : ℤ) (ha : a ≠ 0) (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpaq : ¬ (p : ℤ) ∣ a * q) (K : Type*) [Field K] [NumberField K]
    [IsSplittingField ℚ K (X ^ q - C (a : ℚ))] :
    SplitsCompletely K p ↔ (p ≡ 1 [MOD q] ∧ (a : ZMod p) ^ ((p - 1) / q) = 1) := by
  sorry

end ArtinPrimitiveRoots
