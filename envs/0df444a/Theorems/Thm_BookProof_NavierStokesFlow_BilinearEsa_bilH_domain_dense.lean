-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_BilinearEsa_bilH_domain_dense
-- name    : BookProof.NavierStokesFlow.BilinearEsa.bilH_domain_dense
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:58:47.376995+00:00
-- url     : https://prove2.me/theorems/42463bb9-bf07-42ab-bcea-de984b562660
-- title:
--   `BookProof.NavierStokesFlow.BilinearEsa.bilH_domain_dense` : Dense ((lpFiniteModes (ℕ × J) : Submodule ℂ (L2I (ℕ × J))) : Set (L2I (ℕ × J)))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesBilinearEsa`.
--
--   `BookProof.NavierStokesFlow.BilinearEsa.bilH_domain_dense` : Dense ((lpFiniteModes (ℕ × J) : Submodule ℂ (L2I (ℕ × J))) : Set (L2I (ℕ × J)))
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.BilinearEsa.bilH_domain_dense`.

-- Generated from ChapterNavierStokesBilinearEsa.lean — theorem BookProof.NavierStokesFlow.BilinearEsa.bilH_domain_dense
import Mathlib
import Definitions.Def_ChapterNavierStokesBilinearEsa
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.BilinearEsa


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine

variable {J : Type*}

theorem BookProof.NavierStokesFlow.BilinearEsa.bilH_domain_dense :
    Dense ((lpFiniteModes (ℕ × J) : Submodule ℂ (L2I (ℕ × J))) : Set (L2I (ℕ × J))) := by sorry
