-- Prove2me | Theorems.Thm_CKKSPrecision_FourierUnits_lemma_2_1
-- name    : CKKSPrecision.FourierUnits.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:41:55.482674+00:00
-- url     : https://prove2.me/theorems/6dd6bfdc-30bc-407e-8ab2-0347714df656
-- title:
--   Lemma 2.1 — generators of the cyclotomic unit group
-- statement:
--   Let $m>2$ be any prime power, $K=\mathbb Q(\zeta)$, $R=\mathbb Z[\zeta]$, and let $S$ contain $1$ and one representative of each invertible residue class modulo sign. With $C_m$ and $c_a$ defined above,
--   $$
--   C_m=\langle-1,\zeta,c_a:a\in S\setminus\{1\}\rangle\subset K^\times.
--   $$
--   This identifies generators of the integral cyclotomic unit subgroup for every prime-power conductor, including odd prime powers. Together with the class-number index, it supplies the arithmetic input to the explicit logarithmic basis.
--
--   Differences from the source:
--   - encoding: $K=\mathbb Q(\zeta)$ with the specified primitive complex root → Mathlib splitting field with the distinguished root sent to $\exp(2\pi i/m)$ by a fixed embedding; reason: an isomorphic model of the same field and root, with no additional hypothesis
--   - encoding: $G=(\mathbb Z/m\mathbb Z)^\times/\{\pm1\}$ identified with integer representatives containing $1$ → a finite representative set in $[1,m-1]$ containing $1$ and meeting each sign pair exactly once; reason: least positive residues encode the same quotient; generators are unchanged by reduction modulo the conductor
--   - encoding: a prime-power integer conductor $m>2$ → a positive natural conductor with the same strict inequality and `IsPrimePow` predicate; reason: positivity is already implied by the source inequality, and the predicate is the usual prime-power property
-- source:
--   Zhaoyang Liang, Runkun Liu, Jingwei Fang, Dan Ding, A New Approach to Reducing Modulus Requirements in Homomorphic Computation: Precision Allocation in CKKS, STOC 2027 submission #148 (October 2026), p. 5, Lemma 2.1, citing [Was97, Lemma 8.1] (PDF p. 7)

import Definitions.Def_CKKSPrecision_FourierUnits_arithmetic_model

set_option autoImplicit false

namespace CKKSPrecision.FourierUnits

theorem lemma_2_1 (m : ℕ+) (hm : 2 < (m : ℕ)) (hp : IsPrimePow (m : ℕ))
    (S : Finset ℕ) (hS : IsRepresentatives m S) :
    cyclotomicUnits m = Subgroup.closure {u : (K m)ˣ |
      (u : K m) = -1 ∨ (u : K m) = zeta m ∨
        ∃ a ∈ S, a ≠ 1 ∧ (u : K m) = c m a} := by sorry

end CKKSPrecision.FourierUnits
