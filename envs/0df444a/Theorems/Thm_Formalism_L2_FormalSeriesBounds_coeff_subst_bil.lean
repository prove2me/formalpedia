-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_subst_bil
-- name    : Formalism.L2.FormalSeriesBounds.coeff_subst_bil
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:45:41.705578+00:00
-- url     : https://prove2.me/theorems/c29eb618-202a-4ac4-93fb-1774232beb98
-- title:
--   Formal Series Bounds: coeff subst bil
-- statement:
--   The Formal Series Bounds construction uses the coeff subst bil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L157-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L157-L240

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries
variable {C : Type} [Field C]
variable {τ κ : Type} [Fintype κ]

theorem Formalism.L2.FormalSeriesBounds.coeff_subst_bil {T1 T2 : Set τ} {a : Fin 2 × κ → MvPowerSeries τ C}
    (ha0 : ∀ s, constantCoeff (a s) = 0) (hax : ∀ i, Van T1 (a (0, i))) (haz : ∀ j, Van T2 (a (1, j)))
    {P Q : τ} (hPQ : P ≠ Q) (hQ : Q ∉ T1) (hP : P ∉ T2) {h : MvPowerSeries (Fin 2 × κ) C}
    (hh : ∀ (g : Fin 2) (e : Fin 2 × κ →₀ ℕ), (∀ s ∈ e.support, s.1 ≠ g) → coeff e h = 0) :
    coeff (E2 P Q) (MvPowerSeries.subst a h) =
      ∑ i, ∑ j, coeff (E2 ((0 : Fin 2), i) ((1 : Fin 2), j)) h *
        (coeff (Finsupp.single P 1) (a (0, i)) * coeff (Finsupp.single Q 1) (a (1, j))) := by sorry
