-- Prove2me | Theorems.Thm_Fermion_Dirac_IsCliffordFamily_even
-- name    : Fermion.Dirac.IsCliffordFamily.even
-- status  : Proved
-- author  : @LG
-- created : 2026-11-25T01:21:05.245363+00:00
-- url     : https://prove2.me/theorems/0cd37bfb-9a40-473e-abe2-bd005faed60d
-- title:
--   A Clifford family has even size
-- statement:
--   **A Clifford family has even size.** If $\gamma^\mu$ ($\mu\in\mathrm{Fin}\,1\oplus\mathrm{Fin}\,3$) is a Clifford family of $n\times n$ complex matrices, i.e. $\gamma^\mu\gamma^\nu+\gamma^\nu\gamma^\mu=2\eta^{\mu\nu}I_n$ with $\eta=\mathrm{diag}(1,-1,-1,-1)$, then $n$ is even. Together with the exclusion of size two, this gives the lower-bound half of the theorem that the Dirac gamma matrices need four dimensions.
--
--   **Formalization Note.** The size `n` and the family `γ` are implicit arguments; the hypothesis is `hγ : IsCliffordFamily γ`; the conclusion is `Even n`. The case $n=0$ is included and holds ($0$ is even).
-- source:
--   Physlib, `PhyslibAlpha/Relativity/Fermions/Dirac/MinimalDimension.lean`, `IsCliffordFamily.even` (L96–L105). https://github.com/leanprover-community/physlib/blob/85bb8f5df598f6701be57a70f06e08069e30589c/PhyslibAlpha/Relativity/Fermions/Dirac/MinimalDimension.lean#L96-L105

import Mathlib
import Definitions.Def_minkowskiMatrix
import Definitions.Def_FermionDirac_IsCliffordFamily

open Matrix Complex

namespace Fermion.Dirac.IsCliffordFamily

theorem even {n : ℕ} {γ : Fin 1 ⊕ Fin 3 → Matrix (Fin n) (Fin n) ℂ}
    (hγ : IsCliffordFamily γ) : Even n := by sorry

end Fermion.Dirac.IsCliffordFamily
