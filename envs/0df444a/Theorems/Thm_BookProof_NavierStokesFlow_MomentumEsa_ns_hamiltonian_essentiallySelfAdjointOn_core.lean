-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_MomentumEsa_ns_hamiltonian_essentiallySelfAdjointOn_core
-- name    : BookProof.NavierStokesFlow.MomentumEsa.ns_hamiltonian_essentiallySelfAdjointOn_core
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T19:21:11.895527+00:00
-- url     : https://prove2.me/theorems/14fc4de7-65f8-45c7-b215-1ed30584b232
-- title:
--   `BookProof.NavierStokesFlow.MomentumEsa.ns_hamiltonian_essentiallySelfAdjointOn_core` (d : ℕ) (p q : Fin d → ℕ → ℝ) (H : maxDom (nsSymbol d p q) →ₗ[ℂ] L2I ℕ) (a b cst : ℝ) (hH : Sy
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesMomentumEsa`.
--
--   `BookProof.NavierStokesFlow.MomentumEsa.ns_hamiltonian_essentiallySelfAdjointOn_core` (d : ℕ) (p q : Fin d → ℕ → ℝ) (H : maxDom (nsSymbol d p q) →ₗ[ℂ] L2I ℕ) (a b cst : ℝ) (hH : SymmetricOn (maxDom (nsSymbol d p q)) H) (hcst : 0 ≤ cst) (hrel : ∀ x : maxDom (nsSymbol d p q), ‖H x‖ ^ 2 ≤ a * ‖diagMax (nsSymbol d p q) x‖ ^ 2 + b * ‖(x : L2I ℕ)‖ ^ 2) (hcomm : ∀ x : maxDom (nsSymbol d p q), |commForm H (diagMax (nsSymbol d p q)) x| ≤ cst * quadForm (diagMax (nsSymbol d p q)) x) : EssentiallySelfAdjointOn (lpFiniteModes ℕ) (H.comp (Submodule.inclusion (finiteModes_le_maxDom (nsSymbol d p q))))
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.MomentumEsa.ns_hamiltonian_essentiallySelfAdjointOn_core`.

-- Generated from ChapterNavierStokesMomentumEsa.lean — theorem BookProof.NavierStokesFlow.MomentumEsa.ns_hamiltonian_essentiallySelfAdjointOn_core
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

theorem BookProof.NavierStokesFlow.MomentumEsa.ns_hamiltonian_essentiallySelfAdjointOn_core (d : ℕ) (p q : Fin d → ℕ → ℝ)
    (H : maxDom (nsSymbol d p q) →ₗ[ℂ] L2I ℕ) (a b cst : ℝ)
    (hH : SymmetricOn (maxDom (nsSymbol d p q)) H) (hcst : 0 ≤ cst)
    (hrel : ∀ x : maxDom (nsSymbol d p q),
      ‖H x‖ ^ 2 ≤ a * ‖diagMax (nsSymbol d p q) x‖ ^ 2 + b * ‖(x : L2I ℕ)‖ ^ 2)
    (hcomm : ∀ x : maxDom (nsSymbol d p q),
      |commForm H (diagMax (nsSymbol d p q)) x|
        ≤ cst * quadForm (diagMax (nsSymbol d p q)) x) :
    EssentiallySelfAdjointOn (lpFiniteModes ℕ)
      (H.comp (Submodule.inclusion (finiteModes_le_maxDom (nsSymbol d p q)))) := by sorry
