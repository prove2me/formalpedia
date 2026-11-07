-- Prove2me | Theorems.Thm_DimFreeShadow_lemma_5_6
-- name    : DimFreeShadow.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:02:40.652032+00:00
-- url     : https://prove2.me/theorems/c04b872e-beec-478b-b1a7-a2fb88d2d5ce
-- title:
--   Lemma 5.6 — one unbiased grid-output measurement for all states
-- statement:
--   Fix effects $0\preceq E_1,\dots,E_M\preceq I$ and $\epsilon\in(0,1)$. For a sufficiently large absolute constant $C$, set $N=\lceil C\log(2M)/\epsilon^2\rceil$. There is a $\mathcal Z_\epsilon$-outcome POVM on $\mathcal H^{\otimes N}$, with identity decoder, such that
--
--   $$
--   \sup_{\rho\in\mathcal D(\mathcal H)}\max_{1\le j\le M}|\theta_j(\rho)-\mathbb E_\rho Z_j|\le\epsilon,\qquad\theta_j(\rho)=\operatorname{Tr}(E_j\rho).
--   $$
--
--   The measurement depends only on $\mathcal H$, the known list and $\epsilon$. This is the result of the minimax and net arguments: it holds for all states and not on average over a prior.
--
--   Differences from the source:
--   - encoding: a finite-dimensional Hilbert space H and its tensor powers → ℂ^d for a finite type d, with H^{⊗T} indexed by Fin T → d; reason: every finite-dimensional Hilbert space is unitarily equivalent to some ℂ^d; the same instances
--   - reading: for a sufficiently large absolute constant C → ∃ C₀, ∀ C ≥ C₀, with C₀ chosen before the Hilbert space, M, the effects and ϵ; reason: the standard meaning of "sufficiently large absolute"; this is the strongest reading, valid for all large C
--   - encoding: Z_ϵ with identity decoder → Grid M ϵ with value gridValue z j = k_j / K_ϵ; reason: integer coordinates of the same grid; E_ρ Z_j = Σ_z z_j Tr(N_z ρ^{⊗N})
--   - encoding: Tr(·) of an effect times a state (a real number) → the real part .re of the complex trace; reason: the trace of a product of two Hermitian positive semidefinite matrices is real; the same value
-- source:
--   Jeronimo, Huang, Liu, Dimension-Free Polylogarithmic Quantum Shadow Tomography, arXiv:2608.06345 (sha256 a1a42249…), Lemma 5.6, p.25

import Mathlib
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_DimFreeShadow_gridValue

namespace DimFreeShadow

open ShadowTomography.UpperBound (tensorPow)

/-- **Lemma 5.6 (one unbiased grid-output measurement for all states)** (arXiv:2608.06345,
sha256 a1a42249…, Lemma 5.6, p.25). Fix `0 ⪯ E_1, …, E_M ⪯ I` and `ϵ ∈ (0, 1)`. For a
sufficiently large absolute constant `C`, set `N := ⌈C log(2M)/ϵ²⌉`. There is a `Z_ϵ`-outcome
POVM on `H^{⊗N}`, with identity decoder, such that
`sup_{ρ∈D(H)} max_{1≤j≤M} |θ_j(ρ) − E_ρ Z_j| ≤ ϵ`, `θ_j(ρ) := Tr(E_jρ)` (29). The measurement
depends only on `H`, the known list, and `ϵ`.

**Formalization Note** "For a sufficiently large absolute constant `C`" is
`∃ C₀, ∀ C ≥ C₀`, with `C₀` chosen before the Hilbert space, `M`, the effects and `ϵ`
(absolute). `Z_ϵ` is `Grid M ϵ` (`Fin M → Fin (K_ϵ + 1)`, value `k/K_ϵ`, `K_ϵ = ⌈2/ϵ⌉`), and the
identity decoder gives `E_ρ Z_j = Σ_z z_j Tr(N_z ρ^{⊗N})`. The POVM is chosen before `ρ`.
Natural logarithm; `⌈·⌉` is `Nat.ceil`. -/
theorem lemma_5_6 :
    ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C →
      ∀ (d : Type) [Fintype d] [DecidableEq d] (M : ℕ), 1 ≤ M →
      ∀ E : Fin M → Matrix d d ℂ, (∀ j, QAlgorithms.IsEffect (E j)) →
      ∀ ϵ : ℝ, 0 < ϵ → ϵ < 1 →
        ∃ Nz : Grid M ϵ → Matrix (Fin ⌈C * Real.log (2 * M) / ϵ ^ 2⌉₊ → d)
            (Fin ⌈C * Real.log (2 * M) / ϵ ^ 2⌉₊ → d) ℂ,
          QAlgorithms.IsPOVM Nz ∧
          ∀ ρ : Matrix d d ℂ, WildeQIT.IsDensityOperator ρ → ∀ j : Fin M,
            |(E j * ρ).trace.re -
              ∑ z, gridValue z j * (Nz z * tensorPow ρ ⌈C * Real.log (2 * M) / ϵ ^ 2⌉₊).trace.re|
              ≤ ϵ := by sorry

end DimFreeShadow
