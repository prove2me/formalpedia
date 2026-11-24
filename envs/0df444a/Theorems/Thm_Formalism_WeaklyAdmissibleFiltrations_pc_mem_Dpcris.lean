-- Prove2me | Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_pc_mem_Dpcris
-- name    : Formalism.WeaklyAdmissibleFiltrations.pc_mem_Dpcris
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:39:55.80651+00:00
-- url     : https://prove2.me/theorems/d27cf07c-774a-403b-a9b3-e9ae67c1b541
-- title:
--   Weakly Admissible Filtrations: pc mem Dpcris
-- statement:
--   The Weakly Admissible Filtrations construction uses the pc mem Dpcris property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/DPotCrisStableAndExistsPotentiallyCrystallineDat.lean#L99-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/DPotCrisStableAndExistsPotentiallyCrystallineDat.lean#L99-L102

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_DpcrisStable
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_DPotCrisStableAndExistsPotentiallyCrystallineDat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.WeaklyAdmissibleFiltrations
open Module TensorProduct
variable {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K]
    [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem Formalism.WeaklyAdmissibleFiltrations.pc_mem_Dpcris {x : V ⊗[Qp] B} :
    x ∈ PC.Dpcris ρ ↔ ∀ h : PC.H, actVB PC.PD ρ (h : G) x = x := by sorry
