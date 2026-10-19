-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_MomentumEsa_nsComparison_restrict_eq
-- name    : BookProof.NavierStokesFlow.MomentumEsa.nsComparison_restrict_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:21:10.556561+00:00
-- url     : https://prove2.me/theorems/b4a16577-5338-4955-b635-b804a5826e35
-- title:
--   `BookProof.NavierStokesFlow.MomentumEsa.nsComparison_restrict_eq` (d : ℕ) (p q : Fin d → ℕ → ℝ) : (diagMax (nsSymbol d p q)).comp (Submodule.inclusion (finiteModes_le_maxDom (nsSym
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesMomentumEsa`.
--
--   `BookProof.NavierStokesFlow.MomentumEsa.nsComparison_restrict_eq` (d : ℕ) (p q : Fin d → ℕ → ℝ) : (diagMax (nsSymbol d p q)).comp (Submodule.inclusion (finiteModes_le_maxDom (nsSymbol d p q))) = (lpFiniteModes ℕ).subtype.comp (diagComparisonData d p q).comparison
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.MomentumEsa.nsComparison_restrict_eq`.

-- Generated from ChapterNavierStokesMomentumEsa.lean — theorem BookProof.NavierStokesFlow.MomentumEsa.nsComparison_restrict_eq
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumEsa
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFarisLavineLift
import Definitions.Def_ChapterNavierStokesGaugeY
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.JacobiDeficiency
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData
open BookProof.NavierStokesGaugeY
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumEsa




open LpNat BookProof.FarisLavine IkebeKato FarisLavineLift DiagonalEsa

variable {ι : Type*}

theorem BookProof.NavierStokesFlow.MomentumEsa.nsComparison_restrict_eq (d : ℕ) (p q : Fin d → ℕ → ℝ) :
    (diagMax (nsSymbol d p q)).comp
        (Submodule.inclusion (finiteModes_le_maxDom (nsSymbol d p q)))
      = (lpFiniteModes ℕ).subtype.comp (diagComparisonData d p q).comparison := by sorry
