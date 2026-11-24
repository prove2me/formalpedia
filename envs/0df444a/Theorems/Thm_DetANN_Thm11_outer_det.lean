-- Prove2me | Theorems.Thm_DetANN_Thm11_outer_det
-- name    : DetANN.Thm11.outer_det
-- status  : Proved
-- author  : @milia
-- created : 2026-11-23T21:58:34.444802+00:00
-- url     : https://prove2.me/theorems/9876f9e5-983a-44fa-93d0-6780b761d5fe
-- title:
--   The outer programs of Theorem 1.1 are deterministic
-- statement:
--   For all deterministic programs $\mathrm{Pre}_3,\mathrm{Qry}_3$ and all parameters $n_3,c_0,C_b,K,C_p,X_3\in\mathbb N$, the outer programs
--   $$\mathrm{outerPre}(\mathrm{Pre}_3,n_3,c_0,C_b,K,C_p,X_3)\quad\text{and}\quad\mathrm{outerQry}(\mathrm{Qry}_3,n_3,c_0,C_b,K,C_p,X_3)$$
--   (definition `DetANN_Thm11_OuterProg`) are deterministic programs in the sense of `DetProgram`: their real constants are rational, and they contain no coin, real-power, accept or reject instructions.
--
--   This is the determinism clause of the machine part of Theorem 1.1 (theorem `outer_composition`).
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' for the machine part of DetANN.theorem_1_1 (Feng, Indyk, STOC 2027 submission, Theorem 1.1, p.2; the construction of §7.4, p.19). The machine is PNormReg (definition PNormReg_Machine) with the conventions of DetANN_DataStructure.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_PNormRegLib_AddressBound
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_Construction
import Definitions.Def_DetANN_TupleFamily
import Definitions.Def_DetANN_Thm11_Split
import Definitions.Def_DetANN_Thm11_OuterProg
import Definitions.Def_DetANN_Thm11_Stored

namespace DetANN

namespace Thm11

open PNormReg PNormRegLib

/-- The outer programs are deterministic programs when the inner ones are. -/
theorem outer_det :
    ∀ (Pre₃ Qry₃ : Program) (n3 c0 Cb K Cp X3 : ℕ), DetProgram Pre₃ → DetProgram Qry₃ →
      DetProgram (outerPre Pre₃ n3 c0 Cb K Cp X3) ∧ DetProgram (outerQry Qry₃ n3 c0 Cb K Cp X3) := by
  sorry

end Thm11

end DetANN
