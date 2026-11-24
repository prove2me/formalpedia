-- Prove2me | Theorems.Thm_Formalism_L2_Pj_CompSplitPfD_cspD_disj
-- name    : Formalism.L2.Pj.CompSplitPfD.cspD_disj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:26.38591+00:00
-- url     : https://prove2.me/theorems/3258a621-386b-4dda-87ae-958de2bb1de6
-- title:
--   Comp Split Pf D: csp D disj
-- statement:
--   The Comp Split Pf D construction uses the csp D disj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompSplitPfD.lean#L25-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompSplitPfD.lean#L25-L53

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsGenFrGenFr
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompFin
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompSplitPfC
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompSplitPfD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.CompSplitPfD
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Topology

theorem Formalism.L2.Pj.CompSplitPfD.cspD_disj {X : Type} [TopologicalSpace X] [QuasiSober X] [T0Space X]
    (hloc : ∀ x : X, ∃ (Y : Type) (_ : TopologicalSpace Y) (g : Y → X), IsOpenEmbedding g ∧ x ∈ Set.range g ∧
      ∀ a b y : Y, (∀ a', a' ⤳ a → a' = a) → (∀ b', b' ⤳ b → b' = b) → a ⤳ y → b ⤳ y → a = b)
    (Z Z' : Set X) (hZ : Z ∈ irreducibleComponents X) (hZ' : Z' ∈ irreducibleComponents X) (hne : Z ≠ Z') :
    Disjoint Z Z' := by sorry
