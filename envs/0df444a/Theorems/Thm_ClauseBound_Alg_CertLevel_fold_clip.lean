-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertLevel_fold_clip
-- name    : ClauseBound.Alg.CertLevel.fold_clip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:04:11.142881+00:00
-- url     : https://prove2.me/theorems/a18650a8-7aa2-4c0f-bffb-6d54be0bb220
-- title:
--   Cert Level: fold clip
-- statement:
--   If no number of nodes exceeds M, the cut-off changes nothing in a loop that writes the number of
--   nodes of the step into the state, and the number of nodes in the result is
--   at most M.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L440-L461
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L440-L461

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ClauseBound_Alg_CertLevel
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertLevel
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {α : Type} [Enc α] {P : PiecesF}

theorem ClauseBound.Alg.CertLevel.fold_clip (f : NState → Step → NState) (hf : ∀ st s, (f st s).2.2.1 = s.K) (c : U) (M : ℕ) :
    ∀ (l : List Step) (o : Option NState), (∀ s ∈ l, s.K ≤ M) → (∀ st, o = some st → st.2.2.1 ≤ M) →
      l.foldl (fun o s => cap c none (o.map fun st => f (clip M st) s)) o = l.foldl (fun o s => cap c none (o.map fun st => f st s)) o ∧
        ∀ st, l.foldl (fun o s => cap c none (o.map fun st => f st s)) o = some st → st.2.2.1 ≤ M := by sorry
