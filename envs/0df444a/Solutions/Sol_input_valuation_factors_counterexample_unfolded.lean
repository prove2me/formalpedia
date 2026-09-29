-- Prove2me | solution 1 for input_valuation_factors_counterexample_unfolded
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-09-29T04:56:50.23645+00:00
-- url     : https://prove2.me/submissions/c71e5e12-40c4-4ee9-9cc3-528d18d1ed51

import Mathlib
import Definitions.Def_syracuseOrbitMin

set_option autoImplicit false

noncomputable section

attribute [instance] Classical.propDecidable

-- NOTE (2026-09-29 valfac unfolded-node disproof): this submission defines NO
-- local helper defs. The target node
-- `input_valuation_factors_counterexample_unfolded` is self-contained: its
-- statement unfolds `valVec`/`syrVal`/`valSum` into import-only identifiers
-- (`syracuseStep`, `Nat.factorization`), so there is nothing to redefine
-- (redefinition -> verifier WA on preamble-def collision) and nothing missing
-- (omission of preamble defs -> verifier CE, submissions elaborate without
-- the node preamble in scope). Every identifier below resolves from the two
-- imports above. Copy of the ACCEPTED e664f974/f267af22 valeq recipe.
/-- Positively-phrased counterexample for `input_valuation_factors`
    (`5113665b-d375-4c17-9c96-e9fc5e28620c`, tao-collatz mission), in unfolded
    self-contained form.

    The witness is `n₀ = 1`, `n = 3`, `m = 1`. All hypotheses hold
    (`Odd 3`; the valuation sum is `Nat.factorization (3 * 3 + 1) 2
    = Nat.factorization 10 2 = 1 ≤ 1`), but the valuation vectors differ:
    at the unique `j : Fin 1`, the left vector reads
    `Nat.factorization (3 * syracuseStep^[0] 3 + 1) 2 = Nat.factorization 10 2
    = 1`, while the right vector (residue `3 % 2^1 = 1`) reads
    `Nat.factorization (3 * syracuseStep^[0] 1 + 1) 2 = Nat.factorization 4 2
    = 2`. The residue keeps only the lowest `m` bits, but the valuation
    `ν₂(3n+1)` depends on the bit at position `m` itself. -/
theorem solution : ∃ (n₀ n m : ℕ),
      Odd n ∧ Finset.sum Finset.univ (fun j : Fin n₀ => Nat.factorization (3 * syracuseStep^[j.val] n + 1) 2) ≤ m ∧
        (fun j : Fin n₀ => Nat.factorization (3 * syracuseStep^[j.val] n + 1) 2)
          ≠ (fun j : Fin n₀ => Nat.factorization (3 * syracuseStep^[j.val] (n % 2 ^ m) + 1) 2) := by
  have hL : Nat.factorization (3 * 3 + 1) 2 = 1 := by
    rw [show (3 : ℕ) * 3 + 1 = 10 from by norm_num,
      Nat.factorization_def 10 (by norm_num)]
    have h1dvd : (2 : ℕ) ^ 1 ∣ 10 := by decide
    have h2dvd : ¬ (2 : ℕ) ^ 2 ∣ 10 := by decide
    have g1 : 1 ≤ padicValNat 2 10 :=
      (Nat.pow_dvd_iff_le_padicValNat (p := 2) (k := 1) (n := 10) (by norm_num)
        (by norm_num)).mp h1dvd
    have g2 : ¬ 2 ≤ padicValNat 2 10 := fun hle =>
      h2dvd ((Nat.pow_dvd_iff_le_padicValNat (p := 2) (k := 2) (n := 10) (by norm_num)
        (by norm_num)).mpr hle)
    omega
  have hR : Nat.factorization (3 * 1 + 1) 2 = 2 := by
    rw [show (3 : ℕ) * 1 + 1 = 4 from by norm_num,
      Nat.factorization_def 4 (by norm_num)]
    have h1dvd : (2 : ℕ) ^ 2 ∣ 4 := by decide
    have h2dvd : ¬ (2 : ℕ) ^ 3 ∣ 4 := by decide
    have g1 : 2 ≤ padicValNat 2 4 :=
      (Nat.pow_dvd_iff_le_padicValNat (p := 2) (k := 2) (n := 4) (by norm_num)
        (by norm_num)).mp h1dvd
    have g2 : ¬ 3 ≤ padicValNat 2 4 := fun hle =>
      h2dvd ((Nat.pow_dvd_iff_le_padicValNat (p := 2) (k := 3) (n := 4) (by norm_num)
        (by norm_num)).mpr hle)
    omega
  refine ⟨1, 3, 1, ⟨1, by norm_num⟩, ?_, ?_⟩
  · have hsum : Finset.sum Finset.univ
        (fun j : Fin 1 => Nat.factorization (3 * syracuseStep^[j.val] 3 + 1) 2) = 1 := by
      rw [Finset.sum_eq_single (⟨0, by norm_num⟩ : Fin 1)]
      · exact hL
      · intro b _ hb
        have hbv : b.val = 0 := by
          have hlt := b.isLt
          omega
        have hbeq : b = (⟨0, by norm_num⟩ : Fin 1) := by
          ext
          rw [hbv]
        exact absurd hbeq hb
      · intro hcon
        exact absurd (Finset.mem_univ _) hcon
    rw [hsum]
  · intro heq
    have hmod : (3 : ℕ) % 2 ^ 1 = 1 := by norm_num
    have h2 := congrFun heq (⟨0, by norm_num⟩ : Fin 1)
    rw [hmod] at h2
    have hcontra : Nat.factorization (3 * 3 + 1) 2
        = Nat.factorization (3 * 1 + 1) 2 := h2
    omega

/-- Alias under the published node name: the platform verifier looks up the
    published theorem name in the submission environment. The type ascription
    is REQUIRED: the server's parser rejects `theorem <name> := solution`
    ("unexpected token ':='; expected ':'", submit-1 CE 2026-09-29). -/
theorem input_valuation_factors_counterexample_unfolded :
    ∃ (n₀ n m : ℕ),
      Odd n ∧ Finset.sum Finset.univ (fun j : Fin n₀ => Nat.factorization (3 * syracuseStep^[j.val] n + 1) 2) ≤ m ∧
        (fun j : Fin n₀ => Nat.factorization (3 * syracuseStep^[j.val] n + 1) 2)
          ≠ (fun j : Fin n₀ => Nat.factorization (3 * syracuseStep^[j.val] (n % 2 ^ m) + 1) 2) :=
  solution
