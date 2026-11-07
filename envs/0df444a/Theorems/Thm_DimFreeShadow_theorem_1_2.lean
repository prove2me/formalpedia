-- Prove2me | Theorems.Thm_DimFreeShadow_theorem_1_2
-- name    : DimFreeShadow.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:03:10.781486+00:00
-- url     : https://prove2.me/theorems/caf72983-e6fe-4934-b62b-bd50930e5c17
-- title:
--   Theorem 1.2 — dimension-free polylogarithmic shadow tomography (corrected: $\log M\to\log(2M)$)
-- statement:
--   There is a universal constant $C<\infty$ such that, for every finite-dimensional $\mathcal H$, every $M\ge1$ and observables $E_1,\dots,E_M$ with $0\preceq E_j\preceq I$, and all $0<\varepsilon\le1$ and $0<\delta<1$, there is a (finite-outcome) shadow-tomography strategy with accuracy $\varepsilon$ and failure probability $\delta$ using
--
--   $$
--   T\le C\,\varepsilon^{-2}\log(2M)\log(M/\delta)
--   $$
--
--   copies. The bound is independent of $\dim\mathcal H$: one POVM on $\mathcal H^{\otimes T}$ and one decoder into $[0,1]^M$, chosen before the state, satisfy $\sup_{\rho}\mathbb P_\rho[\max_j|g_j(Z)-\operatorname{Tr}(E_j\rho)|>\varepsilon]\le\delta$. The logarithms are natural.
--
--   This answers Aaronson's question whether shadow tomography admits a dimension-independent copy complexity polylogarithmic in $M$, and it is exponentially better in $M$ than the previous dimension-free bound $O(\sqrt M/\varepsilon^2)$.
--
--   **Formalization Note** The constant $C$ is chosen before the Hilbert space, so the claim is uniform in the dimension. For $M=1$ and $\delta>1/2$ the factor $\log(M/\delta)=\log(1/\delta)$ tends to $0$ as $\delta\to1$, which goes beyond the explicit form Eq. (37). The statement is still true there: when $T$ must be small, a uniformly random output on a grid of spacing $2\varepsilon$, combined with a short Hoeffding estimate, succeeds with probability at least $1-\delta$.
--
--   Differences from the source:
--   - correction: T = O(ε⁻² log(M) log(M/δ)) with a universal constant → T ≤ C ε⁻² log(2M) log(M/δ); reason: the printed rate is 0 at M = 1 and forces T = 0. Counterexample: H = ℂ², M = 1, E₁ = |0⟩⟨0|, ε = δ = 1/4. A 0-copy POVM is a probability vector independent of ρ, and |0⟩⟨0|, |1⟩⟨1| have disjoint success sets, so one of them fails with probability ≥ 1/2 > δ. log(2M) is the paper's own normalization in Eqs. (23) and (37), and it is within a factor 2 of log M for M ≥ 2
--   - encoding: a finite-dimensional Hilbert space H and its tensor powers → ℂ^d for a finite type d, with H^{⊗T} indexed by Fin T → d; reason: every finite-dimensional Hilbert space is unitarily equivalent to some ℂ^d; the same instances
--   - reading: a shadow-tomography strategy (Theorem 1.2; Definition 1.1 allows any outcome set); a finite-outcome collective POVM and decoder (Theorem 5.8) → a POVM with a finite outcome type and a decoder into [0,1]^M; reason: Theorem 5.8 is the same result as Theorem 1.2, and its finite-outcome form is the stronger one
--   - encoding: T = O(·), universal constant C, bound independent of dim H → ∃ C before d, M, the effects, ε and δ, and ∃ T with T ≤ C ε⁻² log(2M) log(M/δ); reason: the meaning of the universal constant in the source
-- source:
--   Jeronimo, Huang, Liu, Dimension-Free Polylogarithmic Quantum Shadow Tomography, arXiv:2608.06345 (sha256 a1a42249…), Theorem 1.2, p.2; Theorem 5.8, p.28; Eq. (37), p.31

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_DimFreeShadow_IsShadowStrategy

namespace DimFreeShadow

/-- **Theorem 1.2 (dimension-free polylogarithmic shadow tomography)** (arXiv:2608.06345,
sha256 a1a42249…, Theorem 1.2, p.2; proved as Theorem 5.8, p.28, explicit form Eq. (37),
p.31), with the copy bound corrected from `log M` to `log(2M)`. There is a universal constant
`C < ∞` such that, for every finite-dimensional `H`, every `M ≥ 1` and observables
`E_1, …, E_M` with `0 ⪯ E_j ⪯ I`, and all `0 < ε ≤ 1` and `0 < δ < 1`, there is a
(finite-outcome) shadow-tomography strategy with accuracy `ε` and failure probability `δ` using
`T ≤ C ε^{−2} log(2M) log(M/δ)` copies. The bound is independent of `dim H`.

**Formalization Note** `C` is chosen before the Hilbert space `ℂ^d` (any finite type `d`), `M`,
the effects, `ε` and `δ`: this is the dimension-free claim. The strategy is `IsShadowStrategy`
(Definition 1.1: a POVM on `H^{⊗T}` with a finite outcome type, a decoder into `[0,1]^M`, and
`P_ρ[max_j |g_j(Z) − Tr(E_jρ)| > ε] ≤ δ` for every density matrix `ρ`). Natural logarithm.
Correction: the printed rate `ε^{−2} log(M) log(M/δ)` vanishes at `M = 1`, forcing `T = 0`,
which is impossible (see the item's description); `log M` is replaced by `log(2M)`, the
paper's own normalization in Eqs. (23) and (37), and `log(M/δ)` is kept. -/
theorem theorem_1_2 :
    ∃ C : ℝ, ∀ (d : Type) [Fintype d] [DecidableEq d] (M : ℕ), 1 ≤ M →
      ∀ E : Fin M → Matrix d d ℂ, (∀ j, QAlgorithms.IsEffect (E j)) →
      ∀ ε δ : ℝ, 0 < ε → ε ≤ 1 → 0 < δ → δ < 1 →
        ∃ T : ℕ, (T : ℝ) ≤ C * ε⁻¹ ^ 2 * Real.log (2 * M) * Real.log (M / δ) ∧
          ∃ (Z : Type) (_ : Fintype Z) (Nz : Z → Matrix (Fin T → d) (Fin T → d) ℂ)
            (g : Z → Fin M → ℝ), IsShadowStrategy E Nz g ε δ := by sorry

end DimFreeShadow
