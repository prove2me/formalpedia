-- Prove2me | solution 1 for groupCohomology.natCard_continuousClasses_ofChar_cycloChar_eq_natCard_units_quot_of_primeLocal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/808aa1f8-101d-5f61-9ae1-3e451ec556dd

import Definitions.Def_ExtEndgame_ProductionDatum
import Theorems.Thm_groupCohomology_natCard_continuousClasses_ofChar_eq_natCard_units_quot
import Theorems.Thm_ExtCitation_exists_isPrimitiveRoot_smul_eq_pow_cycloChar_localGaloisToGlobal
import Theorems.Thm_exists_finiteDimensional_comap_localGaloisToGlobal_iff
import Theorems.Thm_IsAlgClosed_exists_units_pow_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_natCard_continuousClasses_ofChar_cycloChar_eq_natCard_units_quot_of_primeLocal

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation
open scoped IntermediateField Pointwise

theorem solution
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes) (hq : (q : ℕ) = p)
    (adm₁ : Submodule (ZMod p) (H1 (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))))
    (hadm₁ : ∀ x, x ∈ adm₁ ↔
      ∃ c : cocycles₁ (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))),
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ (g s : primeLocalGaloisGroup q),
            primeLocalToGlobal q s ∈ F.fixingSubgroup → c.val (g * s) = c.val g)
        ∧ (H1π _).hom c = x) :
    Nat.card adm₁ = Nat.card ((ℚ_[p])ˣ ⧸ (powMonoidHom p : (ℚ_[p])ˣ →* (ℚ_[p])ˣ).range) := by
  subst hq
  haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
  haveI : IsGalois ℚ_[(q : ℕ)] (PadicAlgCl (q : ℕ)) := IsAlgClosure.isGalois _ _
  obtain ⟨ζ, hζp, hζ⟩ := exists_isPrimitiveRoot_smul_eq_pow_cycloChar_localGaloisToGlobal (q : ℕ) (q : ℕ)
  have hroots : ∀ a : (ℚ_[(q : ℕ)])ˣ, ∃ α : (PadicAlgCl (q : ℕ))ˣ,
      algebraMap ℚ_[(q : ℕ)] (PadicAlgCl (q : ℕ)) (a : ℚ_[(q : ℕ)]) = (α : PadicAlgCl (q : ℕ)) ^ (q : ℕ) := by
    intro a
    obtain ⟨α, hα⟩ := IsAlgClosed.exists_units_pow_eq (Fact.out : (q : ℕ).Prime).pos
      (Units.map (algebraMap ℚ_[(q : ℕ)] (PadicAlgCl (q : ℕ)) : ℚ_[(q : ℕ)] →* PadicAlgCl (q : ℕ)) a)
    exact ⟨α, by rw [← Units.val_pow_eq_pow_val, hα, Units.coe_map, MonoidHom.coe_coe]⟩
  refine natCard_continuousClasses_ofChar_eq_natCard_units_quot
    ((cycloChar (q : ℕ)).comp (localGaloisToGlobal (q : ℕ))) hζp (fun g => hζ g) hroots adm₁
    (fun x => (hadm₁ x).trans (exists_congr fun c => and_congr_left' ?_))
  exact exists_finiteDimensional_comap_localGaloisToGlobal_iff (q : ℕ)
    (fun U => ∀ g s : primeLocalGaloisGroup q, s ∈ U → c.val (g * s) = c.val g)
    (fun _ _ hVU h g s hs => h g s (hVU hs))

end S_groupCohomology_natCard_continuousClasses_ofChar_cycloChar_eq_natCard_units_quot_of_primeLocal
end P2MW
export P2MW.S_groupCohomology_natCard_continuousClasses_ofChar_cycloChar_eq_natCard_units_quot_of_primeLocal (solution)
