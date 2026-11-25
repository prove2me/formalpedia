-- Prove2me | solution 1 for syracuse_affine_word_replacement_gives_smaller_merging_start
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-25T01:00:06.829747+00:00
-- url     : https://prove2.me/submissions/00d9ee05-f1c6-4118-85be-af9e030a31ce

import Theorems.Thm_syracuse_smaller_predecessor_iff_affine_interval
import Theorems.Thm_syracuse_valuation_word_affine_identity
import Mathlib.Data.Nat.ModEq

open Nat

theorem solution (w v : List ℕ) (n : ℕ)
    (hn : ¬ 2 ∣ n)
    (hw : List.ofFn (fun i : Fin w.length =>
      (3*syracuseStep^[i.val] n+1).factorization 2) = w)
    (hv : ∀ a : ℕ, a ∈ v → 0 < a)
    (hlen : v.length=w.length) (hsum : v.sum=w.sum)
    (hgt : syracuseAffineConstant w < syracuseAffineConstant v)
    (hmod : syracuseAffineConstant v % 3^w.length = syracuseAffineConstant w % 3^w.length)
    (hroom : syracuseAffineConstant v+3^w.length ≤ syracuseAffineConstant w+3^w.length*n) :
    ∃ k : ℕ, 0 < k ∧ k < n ∧
      syracuseStep^[w.length] n = syracuseStep^[v.length] k ∧
      List.ofFn (fun i : Fin v.length =>
        (3*syracuseStep^[i.val] k+1).factorization 2) = v := by
  let y := syracuseStep^[w.length] n
  have hyo : ¬2 ∣ y := by
    cases hlen' : w.length with
    | zero => simpa only [y, hlen', Function.iterate_zero, id_eq] using hn
    | succ t =>
      dsimp [y]
      rw [hlen', Function.iterate_succ_apply', syracuseStep]
      exact Nat.not_dvd_ordCompl Nat.prime_two (by omega)
  have ea : 2^v.sum*y = 3^w.length*n+syracuseAffineConstant w := by
    rw [hsum]
    exact syracuse_valuation_word_affine_identity w n hw
  have cert := syracuse_smaller_predecessor_iff_affine_interval v y n hyo hv
  dsimp only at cert
  have modEq : (3^w.length*n+syracuseAffineConstant w)%3^w.length =
      syracuseAffineConstant v%3^w.length := by
    simpa using hmod.symm
  obtain ⟨k,kpos,klt,endpt,word,_⟩ := cert.mp
    (by rw [hlen, ea]; exact ⟨modEq,by omega,by omega⟩)
  exact ⟨k,kpos,klt,endpt.symm,word⟩
