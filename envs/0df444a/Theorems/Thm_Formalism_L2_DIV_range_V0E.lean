-- Prove2me | Theorems.Thm_Formalism_L2_DIV_range_V0E
-- name    : Formalism.L2.DIV.range_V0E
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:46:05.681936+00:00
-- url     : https://prove2.me/theorems/5cb810e6-6fee-472e-873e-4a6a5ded63f1
-- title:
--   DIV: range V0 E
-- statement:
--   The DIV construction uses the range V0 E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L953-L980
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L953-L980

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues

theorem Formalism.L2.DIV.range_V0E {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) {G : Type} [Group G]
    [Fintype G] (r : Representation K G S.Forms) (X : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ)
    (hidem : idemOf X * idemOf X = idemOf X)
    (hcomm : lvlIdem P ψ * idemOf X = idemOf X * lvlIdem P ψ) :
    LinearMap.range (S.V0E r X P ψ).mulVecLin =
      LinearMap.range (S.gaMat r (idemOf X)).mulVecLin ⊓ S.lvlPart r P ψ := by sorry
