-- Prove2me | Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_lattice_zbasis
-- name    : Formalism.L2.Pj.FundamentalDomainD5.lattice_zbasis
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:04:13.525891+00:00
-- url     : https://prove2.me/theorems/2b355b8f-34b8-4942-a830-b1687982b81d
-- title:
--   Fundamental Domain D5: lattice zbasis
-- statement:
--   The Fundamental Domain D5 construction uses the lattice zbasis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/LatticeZbasis.lean#L11-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/LatticeZbasis.lean#L11-L70

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_LatticeZbasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.FundamentalDomainD5
open NumberField Matrix

theorem Formalism.L2.Pj.FundamentalDomainD5.lattice_zbasis {K : Type} [Field K] [NumberField K] {r : ℕ} (L : Submodule (𝓞 K) (Fin r → K))
    (hfg : L.FG) (hspan : Submodule.span K (L : Set (Fin r → K)) = ⊤) :
    ∃ e : Fin (Module.finrank ℚ K * r) → (Fin r → K), (∀ j, e j ∈ L) ∧ LinearIndependent ℚ e ∧
      ∀ v ∈ L, ∃ n : Fin (Module.finrank ℚ K * r) → ℤ, v = ∑ j, (n j : ℚ) • e j := by sorry
