-- Prove2me | Theorems.Thm_ClauseBound_Gen_End_solverOf_poly
-- name    : ClauseBound.Gen.End.solverOf_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:17:04.167655+00:00
-- url     : https://prove2.me/theorems/3707acf4-f878-41c6-8a2c-8c162d3b5466
-- title:
--   End: solver Of poly
-- statement:
--   The solver that a family of pieces gives is polynomial-time, if the pieces are.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/End.lean#L51-L67
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/End.lean#L51-L67

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Alg_Prog
import Definitions.Def_PaddedDescent_F_SideF
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Gen_End
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen
open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen
open ClauseBound.Gen.End

theorem ClauseBound.Gen.End.solverOf_poly {P : PiecesF} (hCS : StCertSolveG P) (hCN : StCertNeedC P) (hNC : StNeedC P) (hP : P.Keeps) : (solverOf P).Poly := by sorry
