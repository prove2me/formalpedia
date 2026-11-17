-- Prove2me | Theorems.Thm_DimFreeShadow_Supplement_theorem_5_5
-- name    : DimFreeShadow.Supplement.theorem_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:03:26.832475+00:00
-- url     : https://prove2.me/theorems/447337e6-f1ff-488d-95fc-290233b0daed
-- title:
--   Theorem 5.5 — worst-case shadow tomography with $O(\log^3(2M/\delta)/\varepsilon^2)$ copies, independent of the dimension
-- statement:
--   Let $\mathcal H$ be a finite-dimensional Hilbert space, $M\ge1$, and $E_1,\dots,E_M$ observables with $0\preceq E_j\preceq I$; let $0<\varepsilon\le1$ and $0<\delta<1$ (the hypotheses of Theorem 1.2).
--
--   **Theorem.** There is a universal constant $C$ such that there is a state-uniform shadow-tomography strategy with accuracy $\varepsilon$ and failure probability $\delta$ using
--
--   $$
--   T\le C\,\frac{\log^3(2M/\delta)}{\varepsilon^2}
--   $$
--
--   copies: one POVM on $\mathcal H^{\otimes T}$ with finitely many outcomes and one decoder into $[0,1]^M$, fixed before the state, such that $\mathbb P_\rho[\max_j|g_j(Z)-\operatorname{Tr}(E_j\rho)|>\varepsilon]\le\delta$ for every state $\rho$. The constant does not depend on $\dim\mathcal H$.
--
--   The paper obtains this bound by uniformizing the full-history guarantee of the sequential posterior PGM (Algorithm 1) through minimax and a trace-distance net; it is the first dimension-free polylogarithmic bound of the paper, before the refinement to $O(\varepsilon^{-2}\log(2M)\log(M/\delta))$ in Theorem 1.2.
--
--   **Formalization Note** The strategy is the published `IsShadowStrategy` (Definition 1.1). $C$ is chosen before the Hilbert space $\mathbb C^d$, $M$, the effects, $\varepsilon$ and $\delta$. Natural logarithm.
--
--   Differences from the source:
--   - encoding: a finite-dimensional Hilbert space H and its tensor powers → ℂ^d for a finite type d, with H^{⊗T} indexed by Fin T → d; reason: every finite-dimensional Hilbert space is unitarily equivalent to some ℂ^d; the same instances
--   - reading: a state-uniform shadow-tomography strategy (Definition 1.1 allows any outcome set) → a POVM with a finite outcome type and a decoder into [0,1]^M; reason: the proof's strategy has the finite outcome set Z_ϵ, the same reading as the published goal Theorem 1.2, and the finite-outcome form is the stronger one
--   - encoding: T = O(log³(2M/δ)/ε²), independent of dim H → ∃ C before d, M, the effects, ε and δ, and ∃ T with T ≤ C ε⁻² log(2M/δ)³; reason: the meaning of the O(·) with a universal constant
-- source:
--   Jeronimo, Huang, Liu, Dimension-Free Polylogarithmic Quantum Shadow Tomography, arXiv:2608.06345 (sha256 a1a42249…), Theorem 5.5, p.25; Theorem 1.2, p.2; Definition 1.1, p.2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_DimFreeShadow_IsShadowStrategy

namespace DimFreeShadow

namespace Supplement

/-- **Theorem 5.5 (worst-case shadow tomography with `O(log³(2M/δ)/ε²)` copies)**
(arXiv:2608.06345, sha256 a1a42249…, Theorem 5.5, p.25). Under the hypotheses of Theorem 1.2
(every finite-dimensional `H`, every `M ≥ 1` and observables `0 ⪯ E_j ⪯ I`, all `0 < ε ≤ 1`
and `0 < δ < 1`), there is a state-uniform shadow-tomography strategy using
`T = O(log³(2M/δ)/ε²)` copies, obtained by uniformizing the full-history guarantee of
Algorithm 1.

**Formalization Note** The `O(·)` is a universal constant `C`, chosen before the Hilbert space
`ℂ^d` (any finite type `d`), `M`, the effects, `ε` and `δ`: the bound is dimension-free, as in
Theorem 1.2. The strategy is the published `IsShadowStrategy` (Definition 1.1: a POVM on
`H^{⊗T}` with a finite outcome type, a decoder into `[0,1]^M`, failure probability at most `δ`
at every density matrix); the paper's construction has the finite outcome set `Z_ϵ`. "Obtained
by uniformizing Algorithm 1" describes the proof and is not a clause. Natural logarithm. -/
theorem theorem_5_5 :
    ∃ C : ℝ, ∀ (d : Type) [Fintype d] [DecidableEq d] (M : ℕ), 1 ≤ M →
      ∀ E : Fin M → Matrix d d ℂ, (∀ j, QAlgorithms.IsEffect (E j)) →
      ∀ ε δ : ℝ, 0 < ε → ε ≤ 1 → 0 < δ → δ < 1 →
        ∃ T : ℕ, (T : ℝ) ≤ C * ε⁻¹ ^ 2 * Real.log (2 * M / δ) ^ 3 ∧
          ∃ (Z : Type) (_ : Fintype Z) (Nz : Z → Matrix (Fin T → d) (Fin T → d) ℂ)
            (g : Z → Fin M → ℝ), IsShadowStrategy E Nz g ε δ := by sorry

end Supplement

end DimFreeShadow
