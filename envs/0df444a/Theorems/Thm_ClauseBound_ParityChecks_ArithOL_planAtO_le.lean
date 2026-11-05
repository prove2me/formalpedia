-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_ArithOL_planAtO_le
-- name    : ClauseBound.ParityChecks.ArithOL.planAtO_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:22:52.196841+00:00
-- url     : https://prove2.me/theorems/d7528f49-5b1f-41f7-8263-558c13cabc3c
-- title:
--   Arith OL: plan At O le
-- statement:
--   The statement at one level: K the number of nodes, K^17 ≤ n < K^(17·C₀).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/ArithOL.lean#L532-L564
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/ArithOL.lean#L532-L564

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_ClauseBound_ParityChecks_Sizes
import Definitions.Def_ClauseBound_ParityChecks_ArithAux
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_ArithR
import Definitions.Def_ClauseBound_TopN_ArithR
import Definitions.Def_ClauseBound_TopN_Budget
import Definitions.Def_ClauseBound_Alg_TopArith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_ClauseBound_ParityChecks_ArithOL
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.ArithOL
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.TopN ClauseBound.TopN.Arith

theorem ClauseBound.ParityChecks.ArithOL.planAtO_le {Idx : Type} [Enc Idx] {S : Solver Idx} (hS : S.Poly) (i : Idx) {e : ℝ} {C C₀ k n n₀ s A₁ : ℕ} (hK : 2 ≤ S.K i) (hn17 : S.K i ^ 17 ≤ n)
    (hlt : n < S.K i ^ (17 * C₀)) (he1 : e ≤ 1) (hs : 1 / (2 : ℝ) ^ s ≤ e) (heK : 1 / Real.logb 2 (S.K i) ^ C₀ ≤ e) (h2 : (2 : ℝ) ^ s ≤ (2 / e) ^ C)
    (hM : ((Wof k (S.K i) s : ℕ) : ℝ) ≤ (A₁ : ℝ) * (S.K i) * e)
    (hrate : ∀ lam B : ℕ, 1 ≤ lam → 1 ≤ B → (S.need (i, List.replicate lam (), List.replicate B ()) : ℝ) ≤
      e * (S.K i : ℝ) ^ 2 * lam + C₀ * (S.K i : ℝ) ^ 2 * Real.logb 2 (S.K i * (lam + B))) :
    (((planAtO S (cO k C C₀) n₀ k n i s).getD n : ℕ) : ℝ) ≤
      (((354 * k * ckN k + ccO k C₀ * A₁ + 1 : ℕ) : ℝ) + ((2 ^ s0K k : ℕ) : ℝ) + (A₁ : ℝ) + ((n₀ ^ C₀ : ℕ) : ℝ)) * n * e * ((s : ℝ) + 1) := by sorry
