-- Prove2me | solution 1 for cyclotomicCharacter_localGaloisToGlobal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/f9f4ab23-227c-5ef7-bcf9-3cc8dfee585c

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_cyclotomicCharacter_localGaloisToGlobal

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

theorem solution (p : ℕ) [Fact p.Prime] (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    cyclotomicCharacter (AlgebraicClosure ℚ) p (localGaloisToGlobal p σ).toRingEquiv =
      cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv := by
  classical
  haveI hQ : ∀ i, HasEnoughRootsOfUnity (AlgebraicClosure ℚ) (p ^ i) := fun i => inferInstance
  haveI hP : ∀ i, HasEnoughRootsOfUnity (PadicAlgCl p) (p ^ i) := fun i => inferInstance
  apply Units.ext
  refine PadicInt.ext_of_toZModPow.mp fun n => ?_
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩

  let ι := padicEmbedding p
  let f : rootsOfUnity (p ^ n) (AlgebraicClosure ℚ) → rootsOfUnity (p ^ n) (PadicAlgCl p) := fun ζ =>
    rootsOfUnity.mkOfPowEq (ι ((ζ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)) (by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, show ((ζ : (AlgebraicClosure ℚ)ˣ) ^ (p ^ n)) = 1 from ζ.2, Units.val_one, map_one])
  have hf : ∀ ζ, ((f ζ : (PadicAlgCl p)ˣ) : PadicAlgCl p) = ι ((ζ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) := fun ζ => rfl
  have hfinj : Function.Injective f := by
    intro ζ₁ ζ₂ h
    have := congrArg (fun z : rootsOfUnity (p ^ n) (PadicAlgCl p) => ((z : (PadicAlgCl p)ˣ) : PadicAlgCl p)) h
    simp only [hf] at this
    exact Subtype.ext (Units.ext (ι.injective this))
  haveI := Fintype.ofFinite (rootsOfUnity (p ^ n) (AlgebraicClosure ℚ))
  haveI := Fintype.ofFinite (rootsOfUnity (p ^ n) (PadicAlgCl p))
  have hfbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hfinj, ?_⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      HasEnoughRootsOfUnity.natCard_rootsOfUnity, HasEnoughRootsOfUnity.natCard_rootsOfUnity]

  set c := ((cyclotomicCharacter (AlgebraicClosure ℚ) p (localGaloisToGlobal p σ).toRingEquiv).val.toZModPow n) with hc
  have hspec : ∀ t ∈ rootsOfUnity (p ^ n) (PadicAlgCl p), σ.toRingEquiv t = ((t : (PadicAlgCl p)ˣ) : PadicAlgCl p) ^ c.val := by
    intro t ht
    obtain ⟨ζ, hζ⟩ := hfbij.2 ⟨t, ht⟩
    have hζt : ι ((ζ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) = (t : PadicAlgCl p) := by
      rw [← hf, hζ]
    have hζpow : (((ζ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)) ^ p ^ n = 1 := by
      rw [← Units.val_pow_eq_pow_val, show ((ζ : (AlgebraicClosure ℚ)ˣ) ^ (p ^ n)) = 1 from ζ.2, Units.val_one]
    have h1 := cyclotomicCharacter.spec p (localGaloisToGlobal p σ).toRingEquiv _ hζpow
    show σ (t : PadicAlgCl p) = _
    rw [← hζt, ← padicEmbedding_localGaloisToGlobal, show (localGaloisToGlobal p σ) ((ζ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
        = (localGaloisToGlobal p σ).toRingEquiv ((ζ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) from rfl, h1, map_pow]
  have hu := modularCyclotomicCharacter.unique (PadicAlgCl p)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity (PadicAlgCl p) (p ^ n)) σ.toRingEquiv hspec
  rw [cyclotomicCharacter.toZModPow p σ.toRingEquiv, ← hu]

end S_cyclotomicCharacter_localGaloisToGlobal
end P2MW
export P2MW.S_cyclotomicCharacter_localGaloisToGlobal (solution)
