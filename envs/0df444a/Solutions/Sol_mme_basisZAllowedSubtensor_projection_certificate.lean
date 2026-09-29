-- Prove2me | solution 1 for mme_basisZAllowedSubtensor_projection_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T07:20:53.906854+00:00
-- url     : https://prove2.me/submissions/550ec986-7925-43e1-a434-627d668fbe98

import Definitions.Def_mme_basis_z_allowed_projection
import Definitions.Def_mme_tensor_rank

universe u

open MME Module

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    (T : TensorObj K 3) {ι : Type u}
    (bZ : Basis ι K (T.V 2)) (allowed : ι → Prop)
    [DecidablePred allowed] :
    TensorObj.Restrict (T.basisZAllowedSubtensor bZ allowed) T ∧
      (T.basisZAllowedGrading bZ allowed).classOf 0 0 = ⊤ ∧
      (T.basisZAllowedGrading bZ allowed).classOf 1 0 = ⊤ ∧
      (T.basisZAllowedGrading bZ allowed).classOf 2 0 =
        Submodule.span K (bZ '' {j | allowed j}) := by
  classical
  constructor
  · refine ⟨fun i ↦
        (T.basisZAllowedGrading bZ allowed).blockProj i 0, ?_⟩
    rfl
  constructor
  · change cwBasisGrade (Module.finBasis K (T.V 0))
        (fun _ ↦ (0 : Fin 2)) 0 = ⊤
    rw [cwBasisGrade]
    convert (Module.finBasis K (T.V 0)).span_eq using 1
    all_goals simp
  constructor
  · change cwBasisGrade (Module.finBasis K (T.V 1))
        (fun _ ↦ (0 : Fin 2)) 0 = ⊤
    rw [cwBasisGrade]
    convert (Module.finBasis K (T.V 1)).span_eq using 1
    all_goals simp
  · change cwBasisGrade bZ (fun j ↦ if allowed j then 0 else 1) 0 =
      Submodule.span K (bZ '' {j | allowed j})
    simp only [cwBasisGrade]
    congr 1
    ext j
    simp
