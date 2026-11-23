-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_isMackey_pi_upper_unipotent_prod_character
-- name    : Formalism.EigenvalueLevelCeiling.isMackey_pi_upper_unipotent_prod_character
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:02.600866+00:00
-- url     : https://prove2.me/theorems/8fadeb0d-67d9-428c-8357-5ad2fa52bf27
-- title:
--   Eigenvalue Level Ceiling: is Mackey pi upper unipotent prod character
-- statement:
--   The Eigenvalue Level Ceiling construction uses the is Mackey pi upper unipotent prod character property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/IsMackeyPiUpperUnipotentProdCharacter.lean#L12-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/IsMackeyPiUpperUnipotentProdCharacter.lean#L12-L22

import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_OnLocal
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_Mirabolic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LemmaGG
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IsMackeyPiUpperUnipotentProdCharacter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues

theorem Formalism.EigenvalueLevelCeiling.isMackey_pi_upper_unipotent_prod_character (K : Type) [Field K] [NumberField K]
    (ι : Type) [Fintype ι] [DecidableEq ι] (k : ι → Type) [∀ v, Field (k v)] [∀ v, Finite (k v)] (n : ℕ)
    (χ : ∀ v, AddChar (k v) (𝓞 K)) (hχ : ∀ v, χ v ≠ 1)
    (P : ∀ v, Subgroup (GL (Fin (n + 1)) (k v))) (U : ∀ v, Subgroup (P v))
    (hP : ∀ v, ∀ h : GL (Fin (n + 1)) (k v), h ∈ P v ↔ IsMirab (h : Matrix (Fin (n + 1)) (Fin (n + 1)) (k v)))
    (hU : ∀ v, ∀ h : P v, h ∈ U v ↔
      IsUniU ((h : GL (Fin (n + 1)) (k v)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (k v))) :
    IsMackey (Subgroup.pi Set.univ U) (fun h : (∀ v, P v) =>
      ∏ v, χ v (supd (((h v : P v) : GL (Fin (n + 1)) (k v)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (k v)))) := by sorry
