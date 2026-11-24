-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_TraceIntegrality_Fr_frames_core
-- name    : Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr.frames_core
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:47:40.701+00:00
-- url     : https://prove2.me/theorems/fc8d0ad5-d4ac-4529-ae8d-76fbcec4851d
-- title:
--   Fr: frames core
-- statement:
--   The Fr construction uses the frames core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL4/PFrCore.lean#L147-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL4/PFrCore.lean#L147-L290

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_EqGlobOfHat
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL4_PFrCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.TraceIntegrality Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr
open Formalism.UG Formalism.UG.CS Formalism.UG.P Formalism.BasicNotions Formalism.L2.GlobalTheoryTheory.Comp
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

theorem Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr.frames_core (σ : E →ₐ[F] E) (J : Matrix n n E) (Lb : Submodule (𝓞 E) (n → E))
    (hLbd : IsLat (dl σ J Lb)) {cls : Type} (Λ : cls → Submodule (𝓞 E) (n → E))
    (hΔ : ∀ c, IsLat (dl σ J (Λ c))) (y : cls → GL n 𝒜)
    (hy : ∀ c, y c ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hyl : ∀ c (u : n → 𝒜), u ∈ hat F (Λ c) ↔ (((y c)⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ u ∈ hat F Lb)
    (M : ℕ) (hM : M ≠ 0) {m : Type} [Fintype m] (b : m → n → E) (hb : ∀ a, b a ∈ dl σ J Lb)
    (hgen : ∀ x ∈ dl σ J Lb, ∃ r : m → 𝓞 E, ∃ z ∈ dl σ J Lb, x = ∑ a, r a • b a + (M : E) • z) :
    ∃ e : cls → m → n → E, (∀ c a, e c a ∈ dl σ J (Λ c)) ∧
      ∀ c c' (G : GL n E), G ∈ UJ (σ : E →+* E) J →
        (∀ x, x ∈ Λ c ↔ (G : Matrix n n E) *ᵥ x ∈ Λ c') →
        (∀ a, ∃ w ∈ dl σ J (Λ c'), (G : Matrix n n E) *ᵥ e c a - e c' a = (M : E) • w) →
        ∃ k : GL n 𝒜, k ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) ∧
          (∀ u : n → 𝒜, u ∈ hat F Lb ↔ (k : Matrix n n 𝒜) *ᵥ u ∈ hat F Lb) ∧
          (∀ u ∈ hat F (dl σ J Lb), ∃ z ∈ hat F (dl σ J Lb), (k : Matrix n n 𝒜) *ᵥ u - u = (M : 𝒜) • z) ∧
          y c' = bc ιA G * y c * k⁻¹ := by sorry
