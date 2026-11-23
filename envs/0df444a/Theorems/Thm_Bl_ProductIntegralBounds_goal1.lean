-- Prove2me | Theorems.Thm_Bl_ProductIntegralBounds_goal1
-- name    : Bl.ProductIntegralBounds.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:59:23.798201+00:00
-- url     : https://prove2.me/theorems/bf35a61c-d5b1-410c-b082-b5316accc184
-- title:
--   Product Integral Bounds: goal1
-- statement:
--   The Product Integral Bounds construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/MultivariateIntegrals/IntegralMv.lean#L56-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/MultivariateIntegrals/IntegralMv.lean#L56-L90

import Mathlib
import Definitions.Def_Lemmata_MultivariateIntegrals_IntegralMv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v w
open Bl Bl.ProductIntegralBounds

theorem Bl.ProductIntegralBounds.goal1 :
  ∀ {K : Type u} [inst : NormedField.{u} K] [IsUltrametricDist.{u} K] {τ : Type w} {ι : Type v} {C : Real},
  LE.le.{0} 0 C →
    ∀ (X Y : ι → MvPowerSeries.{w, u} τ K) (s : Finset.{v} ι),
      (∀ (i : ι), Membership.mem.{v, v} s i → Bl.ProductIntegralBounds.IntegralMv.{u, w} (X i)) →
        (∀ (i : ι), Membership.mem.{v, v} s i → Bl.ProductIntegralBounds.IntegralMv.{u, w} (Y i)) →
          (∀ (i : ι),
              Membership.mem.{v, v} s i →
                Bl.ProductIntegralBounds.Bd.{u, w} C (HSub.hSub.{max u w, max u w, max u w} (X i) (Y i))) →
            Bl.ProductIntegralBounds.Bd.{u, w} C
              (HSub.hSub.{max u w, max u w, max u w} (Finset.prod.{v, max u w} s fun (i : ι) ↦ X i)
                (Finset.prod.{v, max u w} s fun (i : ι) ↦ Y i)) := by sorry
