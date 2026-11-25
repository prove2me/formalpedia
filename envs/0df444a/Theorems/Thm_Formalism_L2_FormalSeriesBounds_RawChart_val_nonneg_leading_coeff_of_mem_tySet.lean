-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_val_nonneg_leading_coeff_of_mem_tySet
-- name    : Formalism.L2.FormalSeriesBounds.RawChart.val_nonneg_leading_coeff_of_mem_tySet
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:30:55.771874+00:00
-- url     : https://prove2.me/theorems/bdd43816-9ee4-4f67-8f73-00dc629bcabb
-- title:
--   Raw Chart: val nonneg leading coeff of mem ty Set
-- statement:
--   The Raw Chart construction uses the val nonneg leading coeff of mem ty Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValNonnegLeadingCoeffOfMemTySet.lean#L107-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValNonnegLeadingCoeffOfMemTySet.lean#L107-L194

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstMemTypeSetOfNonneg
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValNonnegLeadingCoeffOfMemTySet
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
open Formalism.L2.FormalSeriesBounds.RawChart
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

theorem Formalism.L2.FormalSeriesBounds.RawChart.val_nonneg_leading_coeff_of_mem_tySet (V : VF C) (g : Fin 2)
    (hlin : ∀ i (μ : κ →₀ ℕ), μ.degree ≤ 1 →
      MvPowerSeries.coeff μ (X.lg i) = MvPowerSeries.coeff μ (MvPowerSeries.X i : MvPowerSeries κ C))
    (hh : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 0) → MvPowerSeries.coeff e X.h = 0)
    (hsat : ∃ w : κ → I g → C, (∀ x c, V.Ge 0 (w x c)) ∧
      ∀ c c' : I g, ∑ x, X.u g c x * w x c' = if c = c' then 1 else 0)
    (hmis : ∀ (c : I g) (q : JJ I g), X.ty g c ≠ X.ty (1 - g) q → V.Ge 0 (X.sg1 (X.u g c) (X.u (1 - g) q)))
    (x : ℕ → I g ⊕ JJ I g → C) (hx : x ∈ X.TySet V g) (s : ℕ) (h0 : ∀ i < s, x i = 0) (n : I g ⊕ JJ I g) :
    V.Ge 0 (x s n) := by sorry
