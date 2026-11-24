-- Prove2me | Theorems.Thm_Formalism_HF_P_frob_iff_chi
-- name    : Formalism.HF.P.frob_iff_chi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:23:55.530124+00:00
-- url     : https://prove2.me/theorems/63a28cc8-202c-48a2-937a-06ccc0402c68
-- title:
--   P: frob iff chi
-- statement:
--   The P construction uses the frob iff chi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DirichletDensity/DirichletDensityProofs/HostDensity.lean#L29-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DirichletDensity/DirichletDensityProofs/HostDensity.lean#L29-L50

import Mathlib
import Definitions.Def_Formalism_DirichletDensity_Statement
import Definitions.Def_Formalism_CMTypeGalois_HalfTypesFromGeneral
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_HostDensity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal Filter Topology Formalism.Q3
noncomputable section
open Formalism Formalism.HF Formalism.HF.P

theorem Formalism.HF.P.frob_iff_chi (q : Fin 3 → ℕ) (hq : Hyp3 q) (E : Type) [Field E] [NumberField E]
    (α : Fin 3 → E) (hE : IsHost q α) (g : Gal3) (p : ℕ) (hp : p.Prime)
    (hpq : ∀ i, p ≠ q i) :
    (∀ (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : Gal(E/ℚ)),
        IsArithFrobAt ℤ σ P → galSign α σ = g) ↔
      ∀ i, chiQ (q i) p = ((g i : ℤˣ) : ℤ) := by sorry
