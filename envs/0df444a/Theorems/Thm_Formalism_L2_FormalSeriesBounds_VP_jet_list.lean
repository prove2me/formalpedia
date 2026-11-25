-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_jet_list
-- name    : Formalism.L2.FormalSeriesBounds.VP.jet_list
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:39:13.211711+00:00
-- url     : https://prove2.me/theorems/1c72d4fa-0e2b-4749-afe8-88df8643d1d6
-- title:
--   VP: jet list
-- statement:
--   The VP construction uses the jet list property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LogCoordOfDpull.lean#L72-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LogCoordOfDpull.lean#L72-L90

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfLogUnitGerm
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LogCoordOfDpull
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_EqOn_prod
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_prod

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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
open Formalism.L2.FormalSeriesBounds.VP
variable {Y : FBChart C V O dd} {p : ∀ o, PairData Y d (I o)}

theorem Formalism.L2.FormalSeriesBounds.VP.jet_list (hD : DPullSt Y p) {n : ℕ} {ι : Type} (cp : ι → Fin n) (uv : ι → Fin dd → C) (co : ι → WVO I → C)
    (m : ι →₀ ℕ) (f : PS C n dd) :
    ∀ (ls : List ι), (∀ ℓ ∈ ls, m ℓ ≠ 0 → uv ℓ = ∑ w : WVO I, co ℓ w • (Y.raw (p w.1)).u w.2.1 w.2.2) →
    ∀ q : MvPolynomial (Fin n × WVO I) C,
      jetAt0 q (pullN Y p (ls.foldr (fun l g => (DofN (Y.B.FK C) (cp l) (uv l))^[m l] g) f)) =
        jetAt0 (q * (ls.map fun l => (∑ w : WVO I, MvPolynomial.C (co l w) * MvPolynomial.X (cp l, w)) ^ m l).prod)
          (pullN Y p f) := by sorry
