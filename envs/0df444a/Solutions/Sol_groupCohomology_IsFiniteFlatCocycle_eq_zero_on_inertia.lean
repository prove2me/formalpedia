-- Prove2me | solution 1 for groupCohomology.IsFiniteFlatCocycle.eq_zero_on_inertia
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:07:42.375737+00:00
-- url     : https://prove2.me/submissions/13fc9328-5297-40f0-a06e-f724b79d2aff

import Definitions.Def_GroupCohomology_FiniteFlatCocycle
import Theorems.Thm_HopfAlgebra_act_eq_self_of_inertiaTrivialChain_padicInt

set_option autoImplicit false

namespace groupCohomology

/-- An extension with unramified coefficients and constant quotient is unramified
when its cocycle extension has a finite-flat model over the odd prime's integers. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    {W : Type} [AddCommGroup W] [Module (ZMod p) W]
    (ρ : Representation (ZMod p) (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) W)
    (c : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → W)
    (hc : IsFiniteFlatCocycle p ρ c)
    (hρ : ∀ σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p], ∀ w : W, ρ σ w = w) :
    ∀ σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p], c σ = 0 := by
  rcases hc with ⟨H, hH, hHopf, hfin, hflat, hcomm, e, he, hact⟩
  letI := hH
  letI := hHopf
  letI := hfin
  letI := hflat
  letI := hcomm
  let L : AddSubgroup (W × ZMod p) :=
    { carrier := {x | x.2 = 0}
      zero_mem' := rfl
      add_mem' := by intro a b ha hb; change a.2 + b.2 = 0; rw [ha, hb, add_zero]
      neg_mem' := by intro a ha; change -a.2 = 0; rw [ha, neg_zero] }
  let N : Fin 3 → AddSubgroup (W × ZMod p) := ![⊥, L, ⊤]
  have hfix := HopfAlgebra.act_eq_self_of_inertiaTrivialChain_padicInt p hp H
    (W × ZMod p) e he (fun σ x => (ρ σ x.1 + x.2 • c σ, x.2)) hact 2 N
    (by rfl) (by rfl)
    (by intro i; fin_cases i <;> simp [N])
    (by
      intro i σ x hx
      fin_cases i
      · have hx' : x = 0 := hx
        subst x
        simp [N]
      · exact hx
      · trivial)
    (by
      intro i σ hσ x hx
      fin_cases i
      · have hx' : x.2 = 0 := hx
        change (ρ σ x.1 + x.2 • c σ, x.2) - x ∈ (⊥ : AddSubgroup (W × ZMod p))
        simp [Prod.ext_iff, hx', hρ σ hσ x.1]
      · change x.2 - x.2 = 0
        exact sub_self _)
  intro σ hσ
  have h := congrArg Prod.fst (hfix σ hσ (0, 1))
  simpa using h

end groupCohomology
