-- Prove2me | Theorems.Thm_Formalism_L2_G_LevAtG_lamGlob_apply
-- name    : Formalism.L2.G.LevAtG.lamGlob_apply
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:23:46.608923+00:00
-- url     : https://prove2.me/theorems/8497dcde-2ba5-471e-99bf-9fdde3d3c3c0
-- title:
--   Lev At G: lam Glob apply
-- statement:
--   The Lev At G construction uses the lam Glob apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/LevelCharts/AtGLev.lean#L62-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/LevelCharts/AtGLev.lean#L62-L79

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_LevelCharts_AtGGlob
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_LevelCharts_AtGLev
import Theorems.Thm_Formalism_L2_G_mem_placesOver

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain Formalism.UG
open scoped TensorProduct
open Formalism Formalism.L2 Formalism.L2.G
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
variable {σE : E →ₐ[F] E} {J : Matrix (Fin N) (Fin N) E} {gp : Fin 2 → ℕ}
    {splitG : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
      E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F}
    {Lb : Submodule (𝓞 E) (Fin N → E)}
    {Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F))} {k m t j : ℕ}

theorem Formalism.L2.G.LevAtG.lamGlob_apply {Z : Type} [CommGroup Z] (X : LevAtG σE J gp splitG Lb Uloc k m t j) (hg : ∀ i, gp i ≠ 0)
    (ψ0 : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → AddChar (resV F v) Z)
    (χ : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → ℕ → (resV F v)ˣ →* Z)
    (Up : Subgroup (GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
    (hUp : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
      Up ≤ (Uloc v).comap (bc (prV (E := E) v))) (x : Up) :
    X.lamGlob hg ψ0 χ Up hUp x = ∏ i : Fin 2, ∏ v ∈ (placesOver F (gp i)).attach,
      X.lamV i v.1 ((mem_placesOver F (gp i) (hg i) v.1).1 v.2) (ψ0 i v.1 ((mem_placesOver F (gp i) (hg i) v.1).1 v.2))
        (χ i v.1 ((mem_placesOver F (gp i) (hg i) v.1).1 v.2))
        ⟨bc (prV (E := E) v.1) (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
          hUp i v.1 ((mem_placesOver F (gp i) (hg i) v.1).1 v.2) x.2⟩ := by sorry
