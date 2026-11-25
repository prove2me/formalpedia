-- Prove2me | Theorems.Thm_Fermion_Dirac_isLeast_size_isCliffordFamily
-- name    : Fermion.Dirac.isLeast_size_isCliffordFamily
-- status  : Proved
-- author  : @LG
-- created : 2026-11-25T01:37:52.68833+00:00
-- url     : https://prove2.me/theorems/bc79bb4e-3d89-47cd-9896-d570ca3e3085
-- title:
--   The gamma matrices need four dimensions (Dirac, 1928)
-- statement:
--   **The gamma matrices need four dimensions (Dirac, 1928).** The smallest size of a nonempty Clifford family is four: the set
--   $$S=\{\,n\in\mathbb{N}\mid n\neq0\ \text{and there exists a Clifford family of }n\times n\text{ complex matrices}\,\}$$
--   has least element $4$. Concretely, (i) Dirac's $4\times4$ matrices form a Clifford family, so $4\in S$; and (ii) every $n\in S$ satisfies $4\le n$. The exclusion of $n=0$ is necessary because the empty $0\times0$ matrices satisfy the Clifford relation vacuously.
--
--   This is the precise sense in which the Dirac equation forces a four-component wavefunction: no first-order relativistic wave equation of this type exists with fewer than four components in signature $(1,3)$.
--
--   **Formalization Note.** `IsLeast S 4` means $4\in S$ and $\forall n\in S,\ 4\le n$. The predicate `IsCliffordFamily` and the metric `minkowskiMatrix` are the mission's definitions, ported verbatim from Physlib.
-- source:
--   Physlib, `PhyslibAlpha/Relativity/Fermions/Dirac/MinimalDimension.lean`, `isLeast_size_isCliffordFamily` (L162–L167). https://github.com/leanprover-community/physlib/blob/85bb8f5df598f6701be57a70f06e08069e30589c/PhyslibAlpha/Relativity/Fermions/Dirac/MinimalDimension.lean#L162-L167

import Mathlib
import Definitions.Def_minkowskiMatrix
import Definitions.Def_FermionDirac_IsCliffordFamily

open Matrix Complex

namespace Fermion.Dirac

theorem isLeast_size_isCliffordFamily :
    IsLeast {n : ℕ | n ≠ 0 ∧ ∃ γ : Fin 1 ⊕ Fin 3 → Matrix (Fin n) (Fin n) ℂ,
      IsCliffordFamily γ} 4 := by sorry

end Fermion.Dirac
