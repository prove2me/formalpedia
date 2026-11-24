-- Prove2me | Theorems.Thm_Formalism_UG_P_csCovol_column
-- name    : Formalism.UG.P.csCovol_column
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:32:43.347325+00:00
-- url     : https://prove2.me/theorems/3ac8bab2-e2f1-410f-bb42-b83be4be660e
-- title:
--   P: cs Covol column
-- statement:
--   The P construction uses the cs Covol column property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsCovol.lean#L120-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsCovol.lean#L120-L191

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

theorem Formalism.UG.P.csCovol_column
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (M : Submodule (𝓞 K) V) (b : Basis (Fin N) ℤ (Formalism.HermitianLatticesTheory.zmap ι M)) (m : Fin N → V)
    (hm : ∀ i, ι (m i) = b i) (e : 𝓞 K)
    (hdual : ∀ x ∈ Formalism.HermitianLatticesTheory.dual h M, (e : K) • x ∈ M) (n : ℤ) (c : 𝓞 K)
    (hc : algebraMap ℤ (𝓞 K) n = c * e)
    (hG : (Matrix.of fun i k => Algebra.trace ℚ K (h (m i) (m k))).det ≠ 0) (j : Fin N) :
    ∃ a : Fin N → ℤ,
      (Matrix.of fun i k => Algebra.trace ℚ K (h (m i) (m k))) *ᵥ (fun k => (a k : ℚ)) =
        ((n * discr K : ℤ) : ℚ) • Pi.single j (1 : ℚ) := by sorry
