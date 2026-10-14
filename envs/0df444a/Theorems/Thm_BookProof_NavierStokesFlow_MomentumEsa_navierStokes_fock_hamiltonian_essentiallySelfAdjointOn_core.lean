-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_MomentumEsa_navierStokes_fock_hamiltonian_essentiallySelfAdjointOn_core
-- name    : BookProof.NavierStokesFlow.MomentumEsa.navierStokes_fock_hamiltonian_essentiallySelfAdjointOn_core
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T19:22:06.904627+00:00
-- url     : https://prove2.me/theorems/2b1aff0b-1e98-4d37-aaad-5ce566f61cc5
-- title:
--   `BookProof.NavierStokesFlow.MomentumEsa.navierStokes_fock_hamiltonian_essentiallySelfAdjointOn_core` (d : ℕ) (p q : Fin d → ℕ → ℝ) (H : maxDom (nsFockSymbol d p q) →ₗ[ℂ] L2I Config
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesMomentumEsa`.
--
--   `BookProof.NavierStokesFlow.MomentumEsa.navierStokes_fock_hamiltonian_essentiallySelfAdjointOn_core` (d : ℕ) (p q : Fin d → ℕ → ℝ) (H : maxDom (nsFockSymbol d p q) →ₗ[ℂ] L2I Config) (a b cst : ℝ) (hH : SymmetricOn (maxDom (nsFockSymbol d p q)) H) (hcst : 0 ≤ cst) (hrel : ∀ x : maxDom (nsFockSymbol d p q), ‖H x‖ ^ 2 ≤ a * ‖diagMax (nsFockSymbol d p q) x‖ ^ 2 + b * ‖(x : L2I Config)‖ ^ 2) (hcomm : ∀ x : maxDom (nsFockSymbol d p q), |commForm H (diagMax (nsFockSymbol d p q)) x| ≤ cst * quadForm (diagMax (nsFockSymbol d p q)) x) : EssentiallySelfAdjointOn (lpFiniteModes Config) (H.comp (Submodule.inclusion (finiteModes_le_maxDom (nsFockSymbol d p q))))
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.MomentumEsa.navierStokes_fock_hamiltonian_essentiallySelfAdjointOn_core`.

-- Generated from ChapterNavierStokesMomentumEsa.lean — theorem BookProof.NavierStokesFlow.MomentumEsa.navierStokes_fock_hamiltonian_essentiallySelfAdjointOn_core
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesGaugeY
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesGaugeY
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumEsa




open LpNat BookProof.FarisLavine IkebeKato FarisLavineLift DiagonalEsa

variable {ι : Type*}

theorem BookProof.NavierStokesFlow.MomentumEsa.navierStokes_fock_hamiltonian_essentiallySelfAdjointOn_core (d : ℕ)
    (p q : Fin d → ℕ → ℝ)
    (H : maxDom (nsFockSymbol d p q) →ₗ[ℂ] L2I Config) (a b cst : ℝ)
    (hH : SymmetricOn (maxDom (nsFockSymbol d p q)) H) (hcst : 0 ≤ cst)
    (hrel : ∀ x : maxDom (nsFockSymbol d p q),
      ‖H x‖ ^ 2 ≤ a * ‖diagMax (nsFockSymbol d p q) x‖ ^ 2 + b * ‖(x : L2I Config)‖ ^ 2)
    (hcomm : ∀ x : maxDom (nsFockSymbol d p q),
      |commForm H (diagMax (nsFockSymbol d p q)) x|
        ≤ cst * quadForm (diagMax (nsFockSymbol d p q)) x) :
    EssentiallySelfAdjointOn (lpFiniteModes Config)
      (H.comp (Submodule.inclusion (finiteModes_le_maxDom (nsFockSymbol d p q)))) := by sorry
