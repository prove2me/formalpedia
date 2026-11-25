-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp3_fixExp
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp3.fixExp
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T15:20:39.33094+00:00
-- url     : https://prove2.me/theorems/4df711b4-4641-5e7c-9956-e130b32e7426
-- title:
--   CInd Fr Exp3: fix Exp
-- statement:
--   The CInd Fr Exp3 construction uses the fix Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/IsUnitCoeffZero.lean#L138-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/IsUnitCoeffZero.lean#L138-L253

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupLinearSecond
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_LogLowOrderOne
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_BalOf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffAddFirstSecond
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_IsUnitCoeffZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp3
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2c
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt FGLaw)
open ReciprocityTheory.ChartRestriction.G.TB (dLin)
variable {S : Type} [CommRing S] {d : ℕ}
variable [Algebra ℚ S]

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp3.fixExp (G : FGLaw S d) {O : Type} (act : O → Fin d → PS S 1 d)
    (hact : ∀ a i, MvPowerSeries.constantCoeff (act a i) = 0) (bar : O → O) (m : ℕ)
    (U : (Jet S (Fin 2 × Fin d) m)ˣ)
    (h1 : jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => psIn d m (![0, 1] : Fin 2 → Fin 3) (G.F j), fun j => X ((2 : Fin 3), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin d) m) =
      jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin d) m) *
      jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin d) m))
    (hs : jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin d) m) = U)
    (hb : ∀ a, jetSubstP m (fun p : Fin 2 × Fin d =>
        (![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)] :
          Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin d) m) =
      jetSubstP m (fun p : Fin 2 × Fin d =>
        (![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (bar a) j)] :
          Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin d) m)) :
    ∃ c : Fin d → Fin d → S, (∀ i l, c i l = c l i) ∧
      (∀ a, Matrix.transpose (dLin (act a)) * Matrix.of c = Matrix.of c * dLin (act (bar a))) ∧
      (U : Jet S (Fin 2 × Fin d) m) = psJet m (expP (-bilL G c)) := by sorry
