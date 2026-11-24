-- Prove2me | Theorems.Thm_Formalism_UG_P_csCovol_expand
-- name    : Formalism.UG.P.csCovol_expand
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:32:32.916964+00:00
-- url     : https://prove2.me/theorems/7fe9fc50-9188-4e2d-9587-862cb58de35e
-- title:
--   P: cs Covol expand
-- statement:
--   The P construction uses the cs Covol expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsCovol.lean#L91-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsCovol.lean#L91-L118

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsCovol
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module NumberField Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) {N : ℕ}
  (ι : V →+ EuclideanSpace ℝ (Fin N))

theorem Formalism.UG.P.csCovol_expand
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (M : Submodule (𝓞 K) V) (b : Basis (Fin N) ℤ (Formalism.HermitianLatticesTheory.zmap ι M)) (m : Fin N → V)
    (hm : ∀ i, ι (m i) = b i) (z : V) (hz : z ∈ M) :
    ∃ a : Fin N → ℤ, (∀ w : V, Algebra.trace ℚ K (h w z) =
        ∑ j, (a j : ℚ) * Algebra.trace ℚ K (h w (m j))) ∧
      (∀ w : V, Algebra.trace ℚ K (h z w) = ∑ j, (a j : ℚ) * Algebra.trace ℚ K (h (m j) w)) := by sorry
