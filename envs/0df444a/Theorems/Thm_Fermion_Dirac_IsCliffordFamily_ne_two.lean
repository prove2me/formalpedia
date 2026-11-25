-- Prove2me | Theorems.Thm_Fermion_Dirac_IsCliffordFamily_ne_two
-- name    : Fermion.Dirac.IsCliffordFamily.ne_two
-- status  : Open
-- author  : @LG
-- created : 2026-11-25T01:23:59.170996+00:00
-- url     : https://prove2.me/theorems/f6ae014d-7e4f-496d-88d5-c8d592aae652
-- title:
--   There are no $2\times2$ Clifford families
-- statement:
--   **There are no $2\times2$ Clifford families.** If $\gamma$ is a Clifford family of $n\times n$ complex matrices against the Minkowski metric $\eta=\mathrm{diag}(1,-1,-1,-1)$, then $n\neq2$. This is the substantive exclusion in the minimal-dimension theorem: size two would accommodate the three Pauli matrices but not the four anticommuting involutions $\gamma^0, i\gamma^1, i\gamma^2, i\gamma^3$ that a Clifford family produces.
--
--   **Formalization Note.** Implicit `n` and `γ`; hypothesis `hγ : IsCliffordFamily γ`; conclusion `n ≠ 2`.
-- source:
--   Physlib, `PhyslibAlpha/Relativity/Fermions/Dirac/MinimalDimension.lean`, `IsCliffordFamily.ne_two` (L125–L142). https://github.com/leanprover-community/physlib/blob/85bb8f5df598f6701be57a70f06e08069e30589c/PhyslibAlpha/Relativity/Fermions/Dirac/MinimalDimension.lean#L125-L142

import Mathlib
import Definitions.Def_minkowskiMatrix
import Definitions.Def_FermionDirac_IsCliffordFamily

open Matrix Complex

namespace Fermion.Dirac.IsCliffordFamily

theorem ne_two {n : ℕ} {γ : Fin 1 ⊕ Fin 3 → Matrix (Fin n) (Fin n) ℂ}
    (hγ : IsCliffordFamily γ) : n ≠ 2 := by sorry

end Fermion.Dirac.IsCliffordFamily
