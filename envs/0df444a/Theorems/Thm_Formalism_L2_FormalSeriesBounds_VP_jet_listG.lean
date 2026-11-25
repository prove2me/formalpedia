-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_jet_listG
-- name    : Formalism.L2.FormalSeriesBounds.VP.jet_listG
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:20:43.132801+00:00
-- url     : https://prove2.me/theorems/6b68fbe9-cb05-5549-9154-5fc0c672aed9
-- title:
--   VP: jet list G
-- statement:
--   The VP construction uses the jet list G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieValG.lean#L110-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieValG.lean#L110-L130

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfUnitGerm
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValG
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
open Formalism.L2.FormalSeriesBounds.VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  {Var : Type} [Fintype Var] {n : ℕ}
variable (Y : FBChart C V O dd) (M : Var → Fin n × Fin dd → C)

theorem Formalism.L2.FormalSeriesBounds.VP.jet_listG {ι : Type} (cp : ι → Fin n) (uv : ι → Fin dd → C) (co : ι → Var → C) (m : ι →₀ ℕ) (f : PS C n dd) :
    ∀ (ls : List ι), (∀ ℓ ∈ ls, m ℓ ≠ 0 → ∀ b i, ∑ x, co ℓ x * M x (b, i) = if b = cp ℓ then uv ℓ i else 0) →
    ∀ q : MvPolynomial Var C,
      jetAt0 q (linPull Y M (ls.foldr (fun l g => (DofN (Y.B.FK C) (cp l) (uv l))^[m l] g) f)) =
        jetAt0 (q * (ls.map fun l => (∑ x, MvPolynomial.C (co l x) * MvPolynomial.X x) ^ m l).prod)
          (linPull Y M f) := by sorry
