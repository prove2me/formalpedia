-- Prove2me | Theorems.Thm_FermiHubbardMix_proposition_13_2
-- name    : FermiHubbardMix.proposition_13_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:34:47.344665+00:00
-- url     : https://prove2.me/theorems/1e64f48c-5709-4971-9143-8a38f51eebc0
-- title:
--   Proposition 13.2 — the generalized CKG Lindbladian is KMS-detailed-balanced and fixes the Gibbs state
-- statement:
--   Let $\beta>0$, let $H$ be an even Hermitian operator, and let $\mathcal L$ be the Lindbladian of Definition 13.1 built from adjoint-closed families of homogeneous single-site jumps with parameters satisfying (16). Then $\mathcal L$ satisfies KMS detailed balance with respect to the Gibbs state $\sigma=e^{-\beta H}/\operatorname{tr}(e^{-\beta H})$, and $\sigma$ is stationary:
--   $$
--   \mathcal L\bigl(e^{-\beta H}/\operatorname{tr}(e^{-\beta H})\bigr)=0 .
--   $$
--   Stationarity is the first ingredient of the mixing theorem: the semigroup converges to $\sigma$ because $\sigma$ is fixed.
--
--   Differences from the source:
--   - encoding: a fixed ordering of the modes of Λ × [m]; Fock space with operators c_{i,a} → any bijection ord : Λ × Fin m ≃ Fin N; c_k = (γ_{2k} + iγ_{2k+1})/2 from the published Jordan–Wigner Majoranas; reason: the same Fock space and the same CAR operators (proved in the verification files); the paper's results hold for every fixed ordering
--   - encoding: operator-valued integrals (17), (18) and L_diss,B → entrywise Bochner integrals, superoperators as the linear extension of their values on matrix units; reason: the integrands are Gaussian-dominated, so the entrywise integrals are the paper's and the maps are linear
--   - encoding: H a fermionic Hamiltonian on Λ → H an even Hermitian operator; reason: the paper's fermionic Hamiltonians are even and Hermitian
--   - generalization: finite sets B_i ⊆ 𝔄_{{i}} closed under adjoints → a finite family of jumps with sites and an involution adj with B_{adj j} = B_j†; reason: sets are the injective families; repeated jumps paired with their adjoints keep the detailed-balance pairing
--   - encoding: KMS detailed balance L†[·] = ρ^{-1/2} L(ρ^{1/2}(·)ρ^{1/2}) ρ^{-1/2} (Definition C.1) → for all X, Y, tr(X† L[Y]) = tr((ρ^{-1/2} L(ρ^{1/2} X ρ^{1/2}) ρ^{-1/2})† Y), with ρ^{1/2} = CFC.sqrt ρ and ρ^{-1/2} its matrix inverse; reason: the defining property of the Hilbert–Schmidt adjoint, which determines L† uniquely; the Gibbs state is positive definite, so the inverse is the true one
-- source:
--   Bakshi, Moitra, Tan, Algorithmic Aspects of the Fermi–Hubbard Model, arXiv:2604.08408 (held version, sha256 055b8f8f…), Proposition 13.2, p.60

import Mathlib
import Definitions.Def_FermiHubbardMix_ckgLind
import Definitions.Def_FermiHubbardMix_kms
open scoped BigOperators
open Matrix
noncomputable section

namespace FermiHubbardMix

/-- **Proposition 13.2** (Bakshi, Moitra, Tan, *Algorithmic Aspects of the Fermi–Hubbard Model*, arXiv:2604.08408 (held version, sha256 055b8f8f…), p.60). The generalized CKG Lindbladian of Definition 13.1 satisfies
KMS detailed balance (Definition C.1) with respect to the Gibbs state `σ = e^{-βH}/tr(e^{-βH})`, and
`σ` is stationary: `L(σ) = 0`.

**Formalization Note** `H` is any even Hermitian operator ("a fermionic Hamiltonian on `Λ`"), `β > 0`,
and the jumps form an adjoint-closed family of homogeneous single-site operators with parameters
obeying eq. (16) (`CKGFamily.Admissible`). -/
theorem proposition_13_2 {Λ : Type*} {m N : ℕ} (ord : Λ × Fin m ≃ Fin N) {ι : Type*} [Fintype ι]
    (H : Op N) (hH : H.IsHermitian) (hHe : IsEven H) (β : ℝ) (hβ : 0 < β)
    (F : CKGFamily Λ N ι) (hF : F.Admissible ord β) :
    IsKMS (gibbs β H) (ckgLind H β F) ∧ ckgLind H β F (gibbs β H) = 0 := by sorry

end FermiHubbardMix
