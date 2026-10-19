-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_MomentumEsa_fock_ns_hamiltonian_hasZeroDeficiencyOn
-- name    : BookProof.NavierStokesFlow.MomentumEsa.fock_ns_hamiltonian_hasZeroDeficiencyOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:21:36.827565+00:00
-- url     : https://prove2.me/theorems/d3254ced-9572-427a-8687-ea945485b67a
-- title:
--   `BookProof.NavierStokesFlow.MomentumEsa.fock_ns_hamiltonian_hasZeroDeficiencyOn` (n : ℕ → ℝ) (hn : ∀ k, 0 ≤ n k) (H : maxDom (fockSymbol n) →ₗ[ℂ] L2I Config) (Hc : lpFiniteModes Co
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesMomentumEsa`.
--
--   `BookProof.NavierStokesFlow.MomentumEsa.fock_ns_hamiltonian_hasZeroDeficiencyOn` (n : ℕ → ℝ) (hn : ∀ k, 0 ≤ n k) (H : maxDom (fockSymbol n) →ₗ[ℂ] L2I Config) (Hc : lpFiniteModes Config →ₗ[ℂ] lpFiniteModes Config) (hHc : ∀ x : lpFiniteModes Config, ((Hc x : lpFiniteModes Config) : L2I Config) = H (Submodule.inclusion (finiteModes_le_maxDom (fockSymbol n)) x)) (a b cst : ℝ) (hH : SymmetricOn (maxDom (fockSymbol n)) H) (hcst : 0 ≤ cst) (hrel : ∀ x : maxDom (fockSymbol n), ‖H x‖ ^ 2 ≤ a * ‖diagMax (fockSymbol n) x‖ ^ 2 + b * ‖(x : L2I Config)‖ ^ 2) (hcomm : ∀ x : maxDom (fockSymbol n), |commForm H (diagMax (fockSymbol n)) x| ≤ cst * quadForm (diagMax (fockSymbol n)) x) : HasZeroDeficiencyOn (lpFiniteModes Config) Hc
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.MomentumEsa.fock_ns_hamiltonian_hasZeroDeficiencyOn`.

-- Generated from ChapterNavierStokesMomentumEsa.lean — theorem BookProof.NavierStokesFlow.MomentumEsa.fock_ns_hamiltonian_hasZeroDeficiencyOn
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumEsa




open LpNat BookProof.FarisLavine IkebeKato FarisLavineLift DiagonalEsa

variable {ι : Type*}

theorem BookProof.NavierStokesFlow.MomentumEsa.fock_ns_hamiltonian_hasZeroDeficiencyOn (n : ℕ → ℝ) (hn : ∀ k, 0 ≤ n k)
    (H : maxDom (fockSymbol n) →ₗ[ℂ] L2I Config)
    (Hc : lpFiniteModes Config →ₗ[ℂ] lpFiniteModes Config)
    (hHc : ∀ x : lpFiniteModes Config, ((Hc x : lpFiniteModes Config) : L2I Config)
      = H (Submodule.inclusion (finiteModes_le_maxDom (fockSymbol n)) x))
    (a b cst : ℝ)
    (hH : SymmetricOn (maxDom (fockSymbol n)) H) (hcst : 0 ≤ cst)
    (hrel : ∀ x : maxDom (fockSymbol n),
      ‖H x‖ ^ 2 ≤ a * ‖diagMax (fockSymbol n) x‖ ^ 2 + b * ‖(x : L2I Config)‖ ^ 2)
    (hcomm : ∀ x : maxDom (fockSymbol n),
      |commForm H (diagMax (fockSymbol n)) x| ≤ cst * quadForm (diagMax (fockSymbol n)) x) :
    HasZeroDeficiencyOn (lpFiniteModes Config) Hc := by sorry
