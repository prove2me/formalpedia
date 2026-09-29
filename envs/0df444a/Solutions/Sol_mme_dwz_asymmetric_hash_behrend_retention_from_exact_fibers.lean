-- Prove2me | solution 1 for mme_dwz_asymmetric_hash_behrend_retention_from_exact_fibers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T14:02:32.586568+00:00
-- url     : https://prove2.me/submissions/fb369443-c986-425e-b02c-ec81061c2dde

import Mathlib
import Theorems.Thm_mme_behrend_explicit_threeAP_free
import Theorems.Thm_mme_dwz_asymmetric_hash_retention_from_exact_fibers

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {Ω Edge X Y : Type}
    [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    [DecidableEq Edge] [DecidableEq X] [DecidableEq Y]
    (A T : Finset Edge) (x : Edge → X) (y : Edge → Y)
    (N p d : ℕ) (hp : 0 < p) (hmod : 4 * d ≤ p)
    (hx : ∀ a ∈ T, (A.filter (fun b ↦ x b = x a)).card ≤ d)
    (hy : ∀ a ∈ T, (A.filter (fun b ↦ y b = y a)).card ≤ d)
    (hstateCard : Fintype.card Ω = p ^ (N + 3))
    (hhash : ∀ S : Finset ℕ,
      S ⊆ Finset.range (p / 2) →
      ThreeAPFree (S : Set ℕ) →
      ∃ E : Ω → Finset Edge,
        (∀ ω, E ω ⊆ A) ∧
        (∀ a ∈ T,
          (Finset.univ.filter (fun ω : Ω ↦ a ∈ E ω)).card =
            S.card * p ^ (N + 1)) ∧
        ∀ q ∈ (T.product A).filter (fun q ↦
            q.1 ≠ q.2 ∧ (x q.1 = x q.2 ∨ y q.1 = y q.2)),
          (Finset.univ.filter (fun ω : Ω ↦
            q.1 ∈ E ω ∧ q.2 ∈ E ω)).card ≤
              S.card * p ^ N) :
    ∃ S : Finset ℕ, ∃ E : Ω → Finset Edge, ∃ ω : Ω,
      ∃ I : Finset Edge,
        S ⊆ Finset.range (p / 2) ∧
        ThreeAPFree (S : Set ℕ) ∧
        I ⊆ T ∧
        I ⊆ E ω ∧
        (∀ e ∈ I, ∀ e' ∈ E ω,
          x e = x e' ∨ y e = y e' → e = e') ∧
        ((T.card : ℝ) *
            (((p / 2 : ℕ) : ℝ) *
              Real.exp (-4 * Real.sqrt
                (Real.log (((p / 2 : ℕ) : ℝ)))))) /
            (2 * (p : ℝ) ^ 2) ≤
          (I.card : ℝ) := by
  obtain ⟨S, hSrange, hSfree, hSdensity⟩ :=
    mme_behrend_explicit_threeAP_free (p / 2)
  obtain ⟨E, hE, hsingle, hpair⟩ := hhash S hSrange hSfree
  obtain ⟨ω, I, hIT, hIE, hisolated, hI⟩ :=
    mme_dwz_asymmetric_hash_retention_from_exact_fibers
      A T x y E N p S.card d hp hmod hE hx hy hstateCard hsingle hpair
  refine ⟨S, E, ω, I, hSrange, hSfree, hIT, hIE, hisolated, ?_⟩
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hscale :
      ((T.card : ℝ) *
          (((p / 2 : ℕ) : ℝ) *
            Real.exp (-4 * Real.sqrt
              (Real.log (((p / 2 : ℕ) : ℝ)))))) /
          (2 * (p : ℝ) ^ 2) ≤
        ((T.card : ℝ) * (S.card : ℝ)) /
          (2 * (p : ℝ) ^ 2) := by
    gcongr
  exact hscale.trans hI
