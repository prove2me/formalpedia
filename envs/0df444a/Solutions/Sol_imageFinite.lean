-- Prove2me | solution 1 for imageFinite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:12:06.091888+00:00
-- url     : https://prove2.me/submissions/021bd87b-bad0-4aa4-a7e0-db46e89edede

import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic
import Definitions.Def_FriezePatterns_chapter1
import Theorems.Thm_translationInvariance

set_option autoImplicit true

theorem _root_.solution (F : Type*) [Field F] (f : ℕ×ℕ → F) (n: ℕ) [nzPattern_n F f n] : Finite (Set.range f) := by
-- We use i ≤ n instead of 1 ≤ i ≤ n to simplify the induction. Lean also automatically infers that {i : ℕ | i ≤ n} is finite.
  have key : Set.range f = f '' ({i : ℕ | i ≤ n} ×ˢ {m : ℕ | m ≤ n}) := by
    apply Set.ext_iff.mpr
    -- the hard part: L.H.S. is a subset of R.H.S.
    intro x ; apply Iff.intro
    intro hx ; unfold Set.range at hx
    rcases hx with ⟨⟨i, m⟩, hx⟩
    by_cases hi : i ≤ n
    · induction' m using Nat.strong_induction_on with m ih
      by_cases hm : m ≤ n
      · exact ⟨⟨i, m⟩, ⟨⟨hi, hm⟩, hx⟩⟩ -- we can just use (i,m) if m ≤ n
      · simp at hm
        specialize ih (m-(n+1)) (by omega)
        have key := translationInvariance F f n i (by linarith) (m - (n + 1))
        have : m - (n+1) + n + 1 = m := by omega
        simp [this, hx] at key
        exact ih key
    · use ⟨0, 0⟩ ; apply And.intro (by simp) -- if i > n, then f(i,n) = 0, so we can use (0,0)
      rw [@pattern_n.topBordZeros F _ f n _ 0, ← hx, @pattern_n.botBordZeros_n F _ f n _ i m (by linarith)]
    -- now the trivial part
    exact λ ⟨y, hy⟩ => ⟨y, hy.2⟩
  rw [key]
  have : Finite ({i : ℕ | i ≤ n} ×ˢ {m : ℕ | m ≤ n}) := Finite.Set.finite_prod _ _
  exact Finite.Set.finite_image ({i : ℕ | i ≤ n} ×ˢ {m : ℕ | m ≤ n}) f
