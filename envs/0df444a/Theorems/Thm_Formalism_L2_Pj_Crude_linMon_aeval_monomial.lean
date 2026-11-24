-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_linMon_aeval_monomial
-- name    : Formalism.L2.Pj.Crude.linMon_aeval_monomial
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:12.885676+00:00
-- url     : https://prove2.me/theorems/e929e09c-3eaa-4aff-bfde-520f70f4263a
-- title:
--   Crude: lin Mon aeval monomial
-- statement:
--   The Crude construction uses the lin Mon aeval monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeDiv.lean#L173-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeDiv.lean#L173-L211

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeBase
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeDiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {k : Type} [CommRing k] {d n : ℕ}

theorem Formalism.L2.Pj.Crude.linMon_aeval_monomial {ι : Type} [Fintype ι] [DecidableEq ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (φ : ι → PS k n d) (hφ0 : ∀ i, constantCoeff (φ i) = 0) (Good : Set ι)
    (hdual : ∀ l ∈ Good, ∀ l', Lin (cp l) (u l) (φ l') = C (if l = l' then 1 else 0))
    (a α : ι →₀ ℕ) (ha : ∀ l, a l ≠ 0 → l ∈ Good) :
    constantCoeff (LinMon cp u a (MvPolynomial.aeval φ (MvPolynomial.monomial α (1 : k)))) =
      if a = α then ((α.prod fun _ e => e.factorial : ℕ) : k) else 0 := by sorry
