-- Prove2me | Theorems.Thm_DimFreeShadow_corollary_5_7
-- name    : DimFreeShadow.corollary_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:03:07.817137+00:00
-- url     : https://prove2.me/theorems/826afffa-acc5-4590-b5c2-810cec603c6d
-- title:
--   Corollary 5.7 — shadow tomography with $O(\epsilon^{-4}\log(2M)\log(2M/\delta))$ copies
-- statement:
--   For every known list of $M$ effects, every $\epsilon\in(0,1)$ and every $\delta\in(0,1)$, there is a finite-outcome shadow-tomography strategy with accuracy $\epsilon$ and failure probability $\delta$ using at most
--
--   $$
--   O\big(\epsilon^{-4}\log(2M)\log(2M/\delta)\big)
--   $$
--
--   copies. The bound is independent of the Hilbert-space dimension.
--
--   Algorithm 3 calls this corollary at constant accuracy $1/4$ on the block space $\mathcal H^{\otimes k_s}$, which is why dimension-independence matters.
--
--   Differences from the source:
--   - encoding: a finite-dimensional Hilbert space H and its tensor powers → ℂ^d for a finite type d, with H^{⊗T} indexed by Fin T → d; reason: every finite-dimensional Hilbert space is unitarily equivalent to some ℂ^d; the same instances
--   - encoding: at most O(ϵ⁻⁴ log(2M) log(2M/δ)) copies, independent of the dimension → ∃ C, chosen before d, M, the effects, ϵ and δ, and ∃ T with T ≤ C ϵ⁻⁴ log(2M) log(2M/δ); reason: the meaning of a uniform O(·) with an absolute constant
-- source:
--   Jeronimo, Huang, Liu, Dimension-Free Polylogarithmic Quantum Shadow Tomography, arXiv:2608.06345 (sha256 a1a42249…), Corollary 5.7, p.27

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_DimFreeShadow_IsShadowStrategy

namespace DimFreeShadow

/-- **Corollary 5.7 (shadow tomography with `ϵ⁻⁴` copies)** (arXiv:2608.06345, sha256
a1a42249…, Corollary 5.7, p.27). For every known list of `M` effects, every `ϵ ∈ (0, 1)` and
`δ ∈ (0, 1)`, there is a finite-outcome shadow-tomography strategy with accuracy `ϵ` and failure
probability `δ` using at most `O(ϵ^{−4} log(2M) log(2M/δ))` copies. The bound is independent of
the Hilbert-space dimension.

**Formalization Note** `O(·)` is `∃ C` with `C` chosen before the Hilbert space `ℂ^d` (any
finite type `d`), `M`, the effects, `ϵ` and `δ`: dimension-free. The strategy is
`IsShadowStrategy` (Definition 1.1: a finite-outcome POVM on `H^{⊗T}`, a decoder into
`[0,1]^M`, failure probability at most `δ` at every density matrix). Natural logarithm. -/
theorem corollary_5_7 :
    ∃ C : ℝ, ∀ (d : Type) [Fintype d] [DecidableEq d] (M : ℕ), 1 ≤ M →
      ∀ E : Fin M → Matrix d d ℂ, (∀ j, QAlgorithms.IsEffect (E j)) →
      ∀ ϵ δ : ℝ, 0 < ϵ → ϵ < 1 → 0 < δ → δ < 1 →
        ∃ T : ℕ, (T : ℝ) ≤ C * ϵ⁻¹ ^ 4 * Real.log (2 * M) * Real.log (2 * M / δ) ∧
          ∃ (Z : Type) (_ : Fintype Z) (Nz : Z → Matrix (Fin T → d) (Fin T → d) ℂ)
            (g : Z → Fin M → ℝ), IsShadowStrategy E Nz g ϵ δ := by sorry

end DimFreeShadow
