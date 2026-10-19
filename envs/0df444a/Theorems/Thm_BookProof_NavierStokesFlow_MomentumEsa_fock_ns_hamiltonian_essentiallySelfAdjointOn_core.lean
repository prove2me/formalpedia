-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_MomentumEsa_fock_ns_hamiltonian_essentiallySelfAdjointOn_core
-- name    : BookProof.NavierStokesFlow.MomentumEsa.fock_ns_hamiltonian_essentiallySelfAdjointOn_core
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:22:21.52318+00:00
-- url     : https://prove2.me/theorems/437f80bd-dfc2-4b34-8f11-8ceadfa76267
-- title:
--   `BookProof.NavierStokesFlow.MomentumEsa.fock_ns_hamiltonian_essentiallySelfAdjointOn_core` (n : ℕ → ℝ) (hn : ∀ k, 0 ≤ n k) (H : maxDom (fockSymbol n) →ₗ[ℂ] L2I Config) (a b cst : ℝ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesMomentumEsa`.
--
--   `BookProof.NavierStokesFlow.MomentumEsa.fock_ns_hamiltonian_essentiallySelfAdjointOn_core` (n : ℕ → ℝ) (hn : ∀ k, 0 ≤ n k) (H : maxDom (fockSymbol n) →ₗ[ℂ] L2I Config) (a b cst : ℝ) (hH : SymmetricOn (maxDom (fockSymbol n)) H) (hcst : 0 ≤ cst) (hrel : ∀ x : maxDom (fockSymbol n), ‖H x‖ ^ 2 ≤ a * ‖diagMax (fockSymbol n) x‖ ^ 2 + b * ‖(x : L2I Config)‖ ^ 2) (hcomm : ∀ x : maxDom (fockSymbol n), |commForm H (diagMax (fockSymbol n)) x| ≤ cst * quadForm (diagMax (fockSymbol n)) x) : EssentiallySelfAdjointOn (lpFiniteModes Config) (H.comp (Submodule.inclusion (finiteModes_le_maxDom (fockSymbol n))))
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.MomentumEsa.fock_ns_hamiltonian_essentiallySelfAdjointOn_core`.

-- Generated from ChapterNavierStokesMomentumEsa.lean — theorem BookProof.NavierStokesFlow.MomentumEsa.fock_ns_hamiltonian_essentiallySelfAdjointOn_core
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumEsa




open LpNat BookProof.FarisLavine IkebeKato FarisLavineLift DiagonalEsa

variable {ι : Type*}

theorem BookProof.NavierStokesFlow.MomentumEsa.fock_ns_hamiltonian_essentiallySelfAdjointOn_core (n : ℕ → ℝ) (hn : ∀ k, 0 ≤ n k)
    (H : maxDom (fockSymbol n) →ₗ[ℂ] L2I Config) (a b cst : ℝ)
    (hH : SymmetricOn (maxDom (fockSymbol n)) H) (hcst : 0 ≤ cst)
    (hrel : ∀ x : maxDom (fockSymbol n),
      ‖H x‖ ^ 2 ≤ a * ‖diagMax (fockSymbol n) x‖ ^ 2 + b * ‖(x : L2I Config)‖ ^ 2)
    (hcomm : ∀ x : maxDom (fockSymbol n),
      |commForm H (diagMax (fockSymbol n)) x| ≤ cst * quadForm (diagMax (fockSymbol n)) x) :
    EssentiallySelfAdjointOn (lpFiniteModes Config)
      (H.comp (Submodule.inclusion (finiteModes_le_maxDom (fockSymbol n)))) := by sorry
