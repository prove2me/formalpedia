-- Prove2me | Theorems.Thm_Fermion_Dirac_IsCliffordFamily_four_le
-- name    : Fermion.Dirac.IsCliffordFamily.four_le
-- status  : Proved
-- author  : @LG
-- created : 2026-11-25T01:28:30.094398+00:00
-- url     : https://prove2.me/theorems/e343cf35-43cb-44e9-be0f-86dcef185869
-- title:
--   A nonempty Clifford family has size at least four
-- statement:
--   **A nonempty Clifford family has size at least four.** If $\gamma$ is a Clifford family of $n\times n$ complex matrices and $n\neq0$, then $4\le n$. This combines the evenness of the size with the exclusion of size two. The hypothesis $n\neq0$ is necessary: the empty $0\times0$ matrices satisfy the Clifford relation vacuously, so size zero cannot be ruled out by the relation alone.
--
--   **Formalization Note.** Binders: implicit `n`, `γ`; hypothesis `hγ : IsCliffordFamily γ`; hypothesis `hn : n ≠ 0`; conclusion `4 ≤ n`.
-- source:
--   Physlib, `PhyslibAlpha/Relativity/Fermions/Dirac/MinimalDimension.lean`, `IsCliffordFamily.four_le` (L144–L148). https://github.com/leanprover-community/physlib/blob/85bb8f5df598f6701be57a70f06e08069e30589c/PhyslibAlpha/Relativity/Fermions/Dirac/MinimalDimension.lean#L144-L148

import Mathlib
import Definitions.Def_minkowskiMatrix
import Definitions.Def_FermionDirac_IsCliffordFamily

open Matrix Complex

namespace Fermion.Dirac.IsCliffordFamily

theorem four_le {n : ℕ} {γ : Fin 1 ⊕ Fin 3 → Matrix (Fin n) (Fin n) ℂ}
    (hγ : IsCliffordFamily γ) (hn : n ≠ 0) : 4 ≤ n := by sorry

end Fermion.Dirac.IsCliffordFamily
