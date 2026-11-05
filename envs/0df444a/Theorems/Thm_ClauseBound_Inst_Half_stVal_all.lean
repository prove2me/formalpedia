-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_stVal_all
-- name    : ClauseBound.Inst.Half.stVal_all
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T01:54:56.226829+00:00
-- url     : https://prove2.me/theorems/c1832a65-9234-425e-a65c-3e52064165f2
-- title:
--   Half: st Val all
-- statement:
--   With a pad that is long enough, the programs return the entries of the matrices.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfAll.lean#L26-L26
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfAll.lean#L26-L26

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfSpec
import Definitions.Def_ClauseBound_Inst_HalfFact
import Definitions.Def_ClauseBound_Inst_HalfLabs
import Definitions.Def_ClauseBound_Inst_HalfEnc
import Definitions.Def_ClauseBound_Inst_HalfPad
import Definitions.Def_ClauseBound_Inst_HalfPar
import Definitions.Def_ClauseBound_Inst_HalfAll
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half

theorem ClauseBound.Inst.Half.stVal_all : StVal := by sorry
