-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieAlg_key
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg.key
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:47:48.901517+00:00
-- url     : https://prove2.me/theorems/d107d7bb-1f6d-4cbe-85af-064fae2930f6
-- title:
--   Exp Tie Alg: key
-- statement:
--   The Exp Tie Alg construction uses the key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpTieAlg.lean#L202-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpTieAlg.lean#L202-L261

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_MonoVal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieAlg
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {S : Type} [CommRing S]
variable {N d : ℕ}
variable (F : Fin d → PS S 2 d) (φ : Fin d → MvPowerSeries (Fin 1 × Fin N) S)

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg.key (h0 : ∀ j, constantCoeff (φ j) = 0) (w : Fin N → Fin d → S)
    (hlin : ∀ q j, coeff (Finsupp.single ((0 : Fin 1), q) 1) (φ j) = w q j)
    (hhom : ∀ j, subst (fun p : Fin 2 × Fin d => subst (cpy (S := S) p.1) (φ p.2)) (F j) =
      subst (fun r : Fin 1 × Fin N =>
        (X ((0 : Fin 2), r.2) + X ((1 : Fin 2), r.2) : MvPowerSeries (Fin 2 × Fin N) S)) (φ j))
    (q : Fin N) (j : Fin d) :
    pderiv S ((0 : Fin 1), q) (φ j) =
      ∑ i, subst (famL φ) (ev (n := 1) ![pt S d 0, 0] (pderiv S ((1 : Fin 2), i) (F j))) * C (w q i) := by sorry
