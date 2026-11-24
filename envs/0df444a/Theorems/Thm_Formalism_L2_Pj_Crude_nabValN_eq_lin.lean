-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_nabValN_eq_lin
-- name    : Formalism.L2.Pj.Crude.nabValN_eq_lin
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:13.443411+00:00
-- url     : https://prove2.me/theorems/9f3b5247-8c87-4073-80ec-be05d2f2dd5f
-- title:
--   Crude: nab Val N eq lin
-- statement:
--   The Crude construction uses the nab Val N eq lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeOrd.lean#L365-L423
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeOrd.lean#L365-L423

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeBase
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeOrd
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {k : Type} [CommRing k] {d n : ℕ}

theorem Formalism.L2.Pj.Crude.nabValN_eq_lin [Algebra ℚ k] {O : Type} [CommRing O] [StarRing O] (B : FB k d O) (h : PS k 2 d)
    (hg : B.IsCanonGauge k h) (w0 : O) (m : ℕ) (f : PS k n d) {ι : Type} [Fintype ι] (cp : ι → Fin n)
    (u : ι → Fin d → k) (P : MvPolynomial ι k) (N : ℕ) (hP : ∀ a ∈ P.support, a.degree = N)
    (hf : OrdGe N f) :
    nabValN B k h w0 m f cp u P = ∑ a ∈ P.support, P.coeff a * constantCoeff (LinMon cp u a f) := by sorry
