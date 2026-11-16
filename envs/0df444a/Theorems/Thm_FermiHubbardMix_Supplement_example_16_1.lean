-- Prove2me | Theorems.Thm_FermiHubbardMix_Supplement_example_16_1
-- name    : FermiHubbardMix.Supplement.example_16_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:08:01.318871+00:00
-- url     : https://prove2.me/theorems/126dc899-1c23-40f8-81a8-0df301571991
-- title:
--   Example 16.1 (Theorem 1.5) — a two-site Fermi–Hubbard Gibbs state outside the convex hull of Gaussian states
-- statement:
--   For every inverse temperature $\beta>0$ there are onsite repulsions $U_1,U_2\in\mathbb R$ and chemical potentials $\mu_1,\mu_2\in\mathbb R$ such that the Gibbs state $e^{-\beta H}/\mathrm{tr}(e^{-\beta H})$ of the two-site spin-$\tfrac12$ Fermi–Hubbard Hamiltonian
--   $$
--   H=-\sum_{s\in\{\uparrow,\downarrow\}}\bigl(c^\dagger_{1,s}c_{2,s}+c^\dagger_{2,s}c_{1,s}\bigr)+\sum_{i=1}^2\Bigl(U_i\,n_{i,\uparrow}n_{i,\downarrow}+\mu_i\,(n_{i,\uparrow}+n_{i,\downarrow})\Bigr)
--   $$
--   (hopping amplitude $t_{1,2}=1$) is not a convex mixture of fermionic Gaussian states.
--
--   Fermionic Gaussian states here are all states $U\rho_\lambda U^\dagger$ with $U=e^{iH_2}$, $H_2$ a Hermitian quadratic form in the Majorana operators and $\rho_\lambda=2^{-4}\prod_j(I+\lambda_jZ_j)$, $\lambda_j\in[-1,1]$: pure and mixed, of either parity. The example shows that onsite energies inside the regime of the paper's rapid-mixing guarantee can produce Gibbs states outside the Gaussian class.
--
--   **Formalization Note** The Hamiltonian is the base mission's `fhHam` (Example 11.8) on two sites joined by one edge; the same $U,\mu$ work for every ordering of the four modes.
--
--   Differences from the source:
--   - encoding: a Fermi–Hubbard Hamiltonian on 2 sites with hopping t_{1,2} = 1, in a fixed ordering of the modes → ∃ U μ : Fin 2 → ℝ such that for every ordering ord : Fin 2 × Fin 2 ≃ Fin 4, fhHam ord ⊤ (fun _ => 1) U μ; reason: the Hamiltonian is ordering-independent: two orderings differ by a mode permutation, a Gaussian unitary that preserves the Gaussian states and maps one representation of H to the other
--   - encoding: fermionic Gaussian states (not defined in the paper) → FermiCap.Gaussian.IsEvenGaussian on Op 4; reason: the standard class, pure and mixed, of either parity, which the proof explicitly allows
--   - encoding: convex mixture → membership in convexHull ℝ; reason: finite convex mixtures; the Gaussian states form a compact set, so its convex hull is closed
-- source:
--   Bakshi, Moitra, Tan, Algorithmic Aspects of the Fermi–Hubbard Model, arXiv:2604.08408 (held version, sha256 055b8f8f…), Example 16.1, p.70; informal Theorem 1.5, p.5

import Mathlib
import Definitions.Def_FermiHubbardMix_fermiHubbard
import Definitions.Def_FermiHubbardMix_gibbs
import Definitions.Def_FermiCap_Gaussian_States
open scoped BigOperators
open Matrix
noncomputable section

namespace FermiHubbardMix.Supplement

/-- **Example 16.1 (A two-site Fermi–Hubbard example)** = **Theorem 1.5 (Fermi–Hubbard states outside
Gaussian mixtures)** (Bakshi, Moitra, Tan, *Algorithmic Aspects of the Fermi–Hubbard Model*, arXiv:2604.08408 (held version, sha256 055b8f8f…), Example 16.1, p.70; informal Theorem 1.5, p.5). For every `β > 0`
there is a Fermi–Hubbard Hamiltonian on 2 sites with hopping amplitude `t_{1,2} = 1` (and suitably chosen
onsite repulsions `U_i` and chemical potentials `µ_i`) whose Gibbs state at inverse temperature `β` is not
a convex mixture of fermionic Gaussian states.

**Formalization Note** The Hamiltonian is the published spin-1/2 Fermi–Hubbard Hamiltonian
`fhHam` (Example 11.8) on the two sites `Fin 2` joined by one edge (`G = ⊤`), hopping `1`, two spin modes per
site (`N = 4`); the statement holds uniformly for every ordering `ord` of the four modes. Fermionic
Gaussian states (pure or mixed, either parity) are the published `FermiCap.Gaussian.IsEvenGaussian`
(`U ρ_λ U†`, `U = exp(iH₂)` with `H₂` Hermitian quadratic in the Majoranas, `ρ_λ = 2^{-4}∏_j (I + λ_j Z_j)`,
`λ_j ∈ [-1, 1]`); a convex mixture is an element of their convex hull. -/
theorem example_16_1 (β : ℝ) (hβ : 0 < β) :
    ∃ U μ : Fin 2 → ℝ, ∀ ord : Fin 2 × Fin 2 ≃ Fin 4,
      gibbs β (fhHam ord ⊤ (fun _ => 1) U μ).ham ∉
        convexHull ℝ {ρ : Op 4 | FermiCap.Gaussian.IsEvenGaussian ρ} := by sorry

end FermiHubbardMix.Supplement
