-- Prove2me | solution 1 for syracuse_descent_odd_band_2310001_to_2387461
-- status  : ACCEPTED   (prove)
-- author  : @FakeMink
-- created : 2026-10-02T19:22:14.750791+00:00
-- url     : https://prove2.me/submissions/d7cda3de-5d84-4444-b085-12aaf207d054

import Mathlib
import Definitions.Def_syracuseStep

set_option autoImplicit false

/- Task100 source-only first finite-band block. The eight historical
certificate declarations are retained; public coverage skips1269 old indices. -/
namespace CollatzFiniteBandBlock0Draft01

namespace CollatzFiniteDescent

/-- Remove factors of two by division, without evaluating a prime factorization. -/
def stripTwos (x : ℕ) : ℕ :=
  if hx : x = 0 then 0
  else if x % 2 = 0 then stripTwos (x / 2)
  else x
termination_by x
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero hx) (by decide)

/-- The executable division algorithm is exactly the mathematical odd part. -/
theorem stripTwos_eq_ordCompl (x : ℕ) : stripTwos x = ordCompl[2] x := by
  induction x using Nat.strong_induction_on with
  | h x ih =>
      rw [stripTwos]
      split
      · rename_i hx
        subst x
        simp
      · rename_i hx
        split
        · rename_i heven
          rw [ih (x / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hx) (by decide))]
          exact Nat.ordCompl_div_of_dvd Nat.prime_two (Nat.dvd_of_mod_eq_zero heven)
        · rename_i hodd
          symm
          apply (Nat.ordCompl_eq_self_iff_zero_or_not_dvd x Nat.prime_two).mpr
          right
          intro hdvd
          exact hodd (Nat.mod_eq_zero_of_dvd hdvd)

theorem stripTwos_pos {x : ℕ} (hx : 0 < x) : 0 < stripTwos x := by
  rw [stripTwos_eq_ordCompl]
  exact Nat.ordCompl_pos 2 (by omega)

theorem stripTwos_odd {x : ℕ} (hx : 0 < x) : stripTwos x % 2 = 1 := by
  have hn : ¬ 2 ∣ stripTwos x := by
    rw [stripTwos_eq_ordCompl]
    exact Nat.not_dvd_ordCompl Nat.prime_two (by omega)
  have hmod : stripTwos x % 2 < 2 := Nat.mod_lt _ (by decide)
  have hne : stripTwos x % 2 ≠ 0 := fun h => hn (Nat.dvd_of_mod_eq_zero h)
  omega

/-- A factorization-free executable Syracuse step. -/
def fastStep (n : ℕ) : ℕ := stripTwos (3 * n + 1)

theorem fastStep_eq (n : ℕ) : fastStep n = syracuseStep n :=
  stripTwos_eq_ordCompl (3 * n + 1)

theorem fastStep_pos (n : ℕ) : 0 < fastStep n := stripTwos_pos (by omega)

theorem fastStep_odd (n : ℕ) : fastStep n % 2 = 1 := stripTwos_odd (by omega)

/-- Scan at most `fuel` steps from `current`, stopping at the first value below `start`.
The initial value counts as step zero; the value after the last step is also checked. -/
def dropScan (start : ℕ) : ℕ → ℕ → Bool
  | 0, current => decide (current < start)
  | fuel + 1, current =>
      if current < start then true else dropScan start fuel (fastStep current)

theorem dropScan_sound {start fuel current : ℕ}
    (h : dropScan start fuel current = true) :
    ∃ t ≤ fuel, syracuseStep^[t] current < start := by
  induction fuel generalizing current with
  | zero =>
      have hc : current < start := by simpa [dropScan] using h
      exact ⟨0, le_refl 0, hc⟩
  | succ fuel ih =>
      by_cases hc : current < start
      · exact ⟨0, Nat.zero_le _, hc⟩
      · have hnext : dropScan start fuel (fastStep current) = true := by
          simpa [dropScan, hc] using h
        obtain ⟨t, ht, hdrop⟩ := ih hnext
        refine ⟨t + 1, by omega, ?_⟩
        rw [Function.iterate_succ_apply]
        simpa [fastStep_eq] using hdrop

def firstDrop (fuel n : ℕ) : Bool := dropScan n fuel n

theorem firstDrop_sound {fuel n : ℕ} (h : firstDrop fuel n = true) :
    ∃ t ≤ fuel, syracuseStep^[t] n < n := dropScan_sound h

/-- A balanced interval check with bounded recursion depth. Exhausting the depth
rejects a nonempty interval; each accepted leaf evaluates `P` at exactly one index. -/
def checkInterval (P : ℕ → Bool) : ℕ → ℕ → ℕ → Bool
  | 0, _, count => decide (count = 0)
  | depth + 1, base, count =>
      if count = 0 then true
      else if count = 1 then P base
      else
        let left := count / 2
        checkInterval P depth base left &&
          checkInterval P depth (base + left) (count - left)

theorem checkInterval_sound {P : ℕ → Bool} {depth base count : ℕ}
    (h : checkInterval P depth base count = true) :
    ∀ i < count, P (base + i) = true := by
  induction depth generalizing base count with
  | zero =>
      have hc : count = 0 := by simpa [checkInterval] using h
      subst count
      intro i hi
      omega
  | succ depth ih =>
      intro i hi
      by_cases hzero : count = 0
      · omega
      · by_cases hone : count = 1
        · have heq : i = 0 := by omega
          subst i
          simpa [checkInterval, hzero, hone] using h
        · have hs : checkInterval P depth base (count / 2) = true ∧
              checkInterval P depth (base + count / 2) (count - count / 2) = true := by
            simpa [checkInterval, hzero, hone, Bool.and_eq_true] using h
          by_cases hleft : i < count / 2
          · exact ih hs.1 i hleft
          · have hright : i - count / 2 < count - count / 2 := by omega
            have heq : base + count / 2 + (i - count / 2) = base + i := by omega
            simpa only [heq] using ih hs.2 (i - count / 2) hright

end CollatzFiniteDescent

namespace CollatzFiniteDescentChunks

open CollatzFiniteDescent

/-- Check `count` odd inputs whose indices start at `base`, with fuel 512. -/
def offsetCheck (base count : ℕ) : Bool :=
  checkInterval (fun j => firstDrop 512 (1883433 + 2 * j)) 20 base count

theorem offsetCheck_accept {base count : ℕ} (h : offsetCheck base count = true) :
    ∀ i < count, firstDrop 512 (1883433 + 2 * (base + i)) = true :=
  checkInterval_sound h

theorem offsetCheck_sound {base count : ℕ} (h : offsetCheck base count = true) :
    ∀ i < count, ∃ t ≤ 512,
      syracuseStep^[t] (1883433 + 2 * (base + i)) < 1883433 + 2 * (base + i) := by
  intro i hi
  exact firstDrop_sound (offsetCheck_accept h i hi)

/-- A checked interval; its acceptance proof is imported, never recomputed by aggregation. -/
structure CheckedChunk where
  base : ℕ
  count : ℕ
  accepted : offsetCheck base count = true

/-- Adjacent chunks begin exactly where the preceding chunk ends. -/
def Contiguous (start : ℕ) : List CheckedChunk → Prop
  | [] => True
  | c :: cs => c.base = start ∧ Contiguous (start + c.count) cs

instance instDecidableContiguous (start : ℕ) (chunks : List CheckedChunk) :
    Decidable (Contiguous start chunks) :=
  match chunks with
  | [] => inferInstanceAs (Decidable True)
  | c :: cs =>
      letI := instDecidableContiguous (start + c.count) cs
      inferInstanceAs (Decidable (c.base = start ∧ Contiguous (start + c.count) cs))

def totalCount : List CheckedChunk → ℕ
  | [] => 0
  | c :: cs => c.count + totalCount cs

/-- List-sized aggregation of checked adjacent intervals, not an input-sized computation. -/
theorem checkedChunks_accept {start : ℕ} {chunks : List CheckedChunk}
    (hc : Contiguous start chunks) :
    ∀ i < totalCount chunks, firstDrop 512 (1883433 + 2 * (start + i)) = true := by
  induction chunks generalizing start with
  | nil =>
      intro i hi
      simp [totalCount] at hi
  | cons c cs ih =>
      rcases hc with ⟨hbase, htail⟩
      intro i hi
      by_cases hleft : i < c.count
      · simpa only [hbase] using offsetCheck_accept c.accepted i hleft
      · have hright : i - c.count < totalCount cs := by
          simp only [totalCount] at hi
          omega
        have heq : start + c.count + (i - c.count) = start + i := by omega
        simpa only [heq] using ih htail (i - c.count) hright

theorem checkedChunks_sound {start : ℕ} {chunks : List CheckedChunk}
    (hc : Contiguous start chunks) :
    ∀ i < totalCount chunks, ∃ t ≤ 512,
      syracuseStep^[t] (1883433 + 2 * (start + i)) < 1883433 + 2 * (start + i) := by
  intro i hi
  exact firstDrop_sound (checkedChunks_accept hc i hi)

end CollatzFiniteDescentChunks

set_option autoImplicit false

namespace CollatzFiniteDescentChunks

set_option maxRecDepth 4096 in
set_option maxHeartbeats 50000000 in
theorem extensionChunk000_checked : offsetCheck 212015 5000 = true := by decide +kernel

end CollatzFiniteDescentChunks

set_option autoImplicit false

namespace CollatzFiniteDescentChunks

set_option maxRecDepth 4096 in
set_option maxHeartbeats 50000000 in
theorem extensionChunk001_checked : offsetCheck 217015 5000 = true := by decide +kernel

end CollatzFiniteDescentChunks

set_option autoImplicit false

namespace CollatzFiniteDescentChunks

set_option maxRecDepth 4096 in
set_option maxHeartbeats 50000000 in
theorem extensionChunk002_checked : offsetCheck 222015 5000 = true := by decide +kernel

end CollatzFiniteDescentChunks

set_option autoImplicit false

namespace CollatzFiniteDescentChunks

set_option maxRecDepth 4096 in
set_option maxHeartbeats 50000000 in
theorem extensionChunk003_checked : offsetCheck 227015 5000 = true := by decide +kernel

end CollatzFiniteDescentChunks

set_option autoImplicit false

namespace CollatzFiniteDescentChunks

set_option maxRecDepth 4096 in
set_option maxHeartbeats 50000000 in
theorem extensionChunk004_checked : offsetCheck 232015 5000 = true := by decide +kernel

end CollatzFiniteDescentChunks

set_option autoImplicit false

namespace CollatzFiniteDescentChunks

set_option maxRecDepth 4096 in
set_option maxHeartbeats 50000000 in
theorem extensionChunk005_checked : offsetCheck 237015 5000 = true := by decide +kernel

end CollatzFiniteDescentChunks

set_option autoImplicit false

namespace CollatzFiniteDescentChunks

set_option maxRecDepth 4096 in
set_option maxHeartbeats 50000000 in
theorem extensionChunk006_checked : offsetCheck 242015 5000 = true := by decide +kernel

end CollatzFiniteDescentChunks

set_option autoImplicit false

namespace CollatzFiniteDescentChunks

set_option maxRecDepth 4096 in
set_option maxHeartbeats 50000000 in
theorem extensionChunk007_checked : offsetCheck 247015 5000 = true := by decide +kernel

end CollatzFiniteDescentChunks

namespace CollatzFiniteDescentChunks

def block0Chunks : List CheckedChunk :=
  [⟨212015, 5000, extensionChunk000_checked⟩,
   ⟨217015, 5000, extensionChunk001_checked⟩,
   ⟨222015, 5000, extensionChunk002_checked⟩,
   ⟨227015, 5000, extensionChunk003_checked⟩,
   ⟨232015, 5000, extensionChunk004_checked⟩,
   ⟨237015, 5000, extensionChunk005_checked⟩,
   ⟨242015, 5000, extensionChunk006_checked⟩,
   ⟨247015, 5000, extensionChunk007_checked⟩]

theorem block0_contiguous : Contiguous 212015 block0Chunks := by
  decide +kernel

theorem block0_count : totalCount block0Chunks = 40000 := by
  decide +kernel

theorem block0_trimmed_descent (i : ℕ) (hi : i < 38731) :
    ∃ t ≤ 512,
      syracuseStep^[t] (2310001 + 2 * i) < 2310001 + 2 * i := by
  have hindex : 1269 + i < totalCount block0Chunks := by
    rw [block0_count]
    omega
  have hdescent := checkedChunks_sound block0_contiguous (1269 + i) hindex
  have hinput :
      1883433 + 2 * (212015 + (1269 + i)) = 2310001 + 2 * i := by
    omega
  rw [hinput] at hdescent
  exact hdescent

end CollatzFiniteDescentChunks

end CollatzFiniteBandBlock0Draft01

theorem solution (i : ℕ) (hi : i < 38731) :
    ∃ t ≤ 512,
      syracuseStep^[t] (2310001 + 2 * i) < 2310001 + 2 * i := by
  exact CollatzFiniteBandBlock0Draft01.CollatzFiniteDescentChunks.block0_trimmed_descent i hi
