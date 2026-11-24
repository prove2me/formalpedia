-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_div_Lin_iter_aeval
-- name    : Formalism.L2.Pj.Crude.div_Lin_iter_aeval
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:21.477797+00:00
-- url     : https://prove2.me/theorems/878bfae3-4bc6-44cf-8696-f4bfb878e58d
-- title:
--   Crude: div Lin iter aeval
-- statement:
--   The Crude construction uses the div Lin iter aeval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeDiv.lean#L93-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeDiv.lean#L93-L99

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

theorem Formalism.L2.Pj.Crude.div_Lin_iter_aeval {ι : Type} [DecidableEq ι] (cp : ι → Fin n) (u : ι → Fin d → k) (φ : ι → PS k n d)
    (l : ι) (hl : ∀ l', Lin (cp l) (u l) (φ l') = C (if l = l' then 1 else 0)) (t : ℕ) (Q : MvPolynomial ι k) :
    (Lin (cp l) (u l))^[t] (MvPolynomial.aeval φ Q) = MvPolynomial.aeval φ ((MvPolynomial.pderiv l)^[t] Q) := by sorry
