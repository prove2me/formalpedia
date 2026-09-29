-- Prove2me | solution 1 for exists_commute_mul_eq_orderOf_coprime_pow_prime_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/8c1d5e4c-86a5-5870-9089-19f02a0c1247

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_exists_commute_mul_eq_orderOf_coprime_pow_prime_pow_eq_one

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module"
open scoped Classical

namespace ArtIndPPart

lemma zpow_mul_zpow_eq_self {G : Type} [Group G] (g : G) (x y m q : ℤ)
    (hxy : x * m + y * q = 1) : g ^ (y * q) * g ^ (x * m) = g := by
  rw [← zpow_add, show y * q + x * m = 1 by linarith, zpow_one]

lemma zpow_mul_orderOf_mul (G : Type) [Group G] (g : G) (c : ℤ) :
    g ^ (c * (orderOf g : ℤ)) = 1 := by
  rw [mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]

end ArtIndPPart

open ArtIndPPart in
theorem solution
    (p : ℕ) [Fact p.Prime] {G : Type} [Group G] [Finite G] (g : G) :
    ∃ g' u : G, g' * u = g ∧ Commute g' u ∧ (orderOf g').Coprime p ∧ (∃ a : ℕ, u ^ p ^ a = 1) ∧
      g' ∈ Subgroup.zpowers g ∧ u ∈ Subgroup.zpowers g := by
  have hp : p.Prime := Fact.out
  have hn0 : orderOf g ≠ 0 := (orderOf_pos g).ne'

  have hqm : p ^ (orderOf g).factorization p * (orderOf g / p ^ (orderOf g).factorization p)
      = orderOf g := Nat.ordProj_mul_ordCompl_eq_self (orderOf g) p
  have hcop : (orderOf g / p ^ (orderOf g).factorization p).Coprime p :=
    (Nat.coprime_ordCompl hp hn0).symm
  set a : ℕ := (orderOf g).factorization p with ha
  set q : ℕ := p ^ a with hq
  set m : ℕ := orderOf g / q with hm
  have hmq : m.Coprime q := hcop.pow_right a
  obtain ⟨x, y, hxy⟩ := Nat.isCoprime_iff_coprime.mpr hmq
  have hqmZ : (q : ℤ) * (m : ℤ) = (orderOf g : ℤ) := by exact_mod_cast hqm
  refine ⟨g ^ (y * q), g ^ (x * m), zpow_mul_zpow_eq_self g x y m q hxy,
    Commute.zpow_zpow_self g _ _, ?_, ⟨a, ?_⟩,
    Subgroup.mem_zpowers_iff.mpr ⟨_, rfl⟩, Subgroup.mem_zpowers_iff.mpr ⟨_, rfl⟩⟩
  ·
    have h1 : (g ^ ((y : ℤ) * q)) ^ m = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_assoc, hqmZ]
      exact zpow_mul_orderOf_mul G g y
    exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h1) hcop
  ·
    show (g ^ ((x : ℤ) * m)) ^ q = 1
    rw [← zpow_natCast, ← zpow_mul, mul_assoc, mul_comm (m : ℤ), hqmZ]
    exact zpow_mul_orderOf_mul G g x

end S_exists_commute_mul_eq_orderOf_coprime_pow_prime_pow_eq_one
end P2MW
export P2MW.S_exists_commute_mul_eq_orderOf_coprime_pow_prime_pow_eq_one (solution)
