-- Prove2me | solution 1 for markov_inequality
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T07:11:39.368622+00:00
-- url     : https://prove2.me/submissions/fffb2b62-101d-4c1f-8b6d-9419d93c3f22

import Mathlib
import Theorems.Thm_markov_unit

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hf : ∀ x, |x| ≤ 1 → |f x| ≤ 1)
    (hpoly : ∃ p : Polynomial ℝ, p.natDegree = n ∧ ∀ x, p.eval x = f x) :
    ∀ x : ℝ, |x| ≤ 1 → |deriv f x| ≤ n ^ 2 := by
  obtain ⟨p, hdeg, hpf⟩ := hpoly
  have hfp : f = fun x => p.eval x := by
    funext x
    exact (hpf x).symm
  subst hfp
  intro x hx
  rw [Polynomial.deriv]
  exact markov_unit p hdeg.le (fun y hy1 hy2 => hf y (abs_le.mpr ⟨hy1, hy2⟩)) x
    (abs_le.mp hx).1 (abs_le.mp hx).2

#print axioms solution
