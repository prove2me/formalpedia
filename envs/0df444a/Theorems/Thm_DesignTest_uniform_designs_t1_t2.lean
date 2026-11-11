-- Prove2me | Theorems.Thm_DesignTest_uniform_designs_t1_t2
-- name    : DesignTest.uniform_designs_t1_t2
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:13:18.055825+00:00
-- url     : https://prove2.me/theorems/f4221a8b-9bca-4a35-91e7-c508374df8a7
-- title:
--   Proof of Cor. 4.17 — an orthonormal basis is an exact 1-design; a complete MUB set has $F^{\mathrm{st}}_2=1/D_{\mathrm{Sym}}$ and is an exact 2-design
-- statement:
--   1. For $d\ge2$, the uniform measure on an orthonormal basis of $\mathbb C^d$ is an exact state $1$-design: $\mathrm{Dist}_1^{(1)}(\mathsf H,\nu_0)=0$.
--   2. For $d\ge2$, let $B_0,\dots,B_d$ be $d+1$ pairwise mutually unbiased orthonormal bases of $\mathbb C^d$ and let $\nu_0$ be the uniform measure on their $L=d(d+1)=2D_{\mathrm{Sym}}$ vectors $|\varphi_j\rangle$. Then
--   $$F^{\mathrm{st}}_2(\nu_0)=\frac1{L^2}\sum_{j,k}|\langle\varphi_j|\varphi_k\rangle|^4=\frac2L=\frac1{D_{\mathrm{Sym}}},$$
--   and $\nu_0$ is an exact state $2$-design: $\mathrm{Dist}_1^{(2)}(\mathsf H,\nu_0)=0$.
--
--   These are the small uniform exact designs ($L=D_{\mathrm{Sym}}$ for $t=1$, $L=2D_{\mathrm{Sym}}$ for $t=2$) that Theorem 4.16 turns into inverse-square sample lower bounds.
--
--   **Formalization Note** Clause 2 is stated for every $d\ge2$ that admits a complete set of mutually unbiased bases; such a set exists for prime powers by Wootters–Fields (milestone `mub_exists_prime_power`). Uniform measures count the $d(d+1)$ vectors with multiplicity, indexed by (basis, element).
--
--   Differences from the source:
--   - generalization: t = 2 and prime-power d, with the complete set of d + 1 mutually unbiased bases of [WF89] → every d ≥ 2 and every family of d + 1 pairwise mutually unbiased orthonormal bases; reason: for prime-power d such a family exists (mub_exists_prime_power), so the Lean statement specializes to the source's
--   - encoding: pure states P(d) are rank-one density matrices |ψ⟩⟨ψ|, and inputs are probability measures on P(d) → pure states are unit vectors of ℂ^d (PureVec d) and inputs are probability measures on the unit sphere; reason: |ψ⟩⟨ψ| is determined by ψ, and every moment operator depends on ψ only through |ψ⟩⟨ψ|; every measure on P(d) lifts to the sphere
--   - encoding: H is the unique unitarily invariant probability measure on P(d) (Definition 3.10) → haarState d, the normalized surface measure on the unit sphere of ℂ^d; reason: its image under ψ ↦ |ψ⟩⟨ψ| is the unitarily invariant probability measure on P(d), so it has the same moment operators
--   - encoding: trace norm ‖A‖₁ = Tr|A| → DistQuantumQuery.traceNorm A = Σ_i √λ_i(A†A), the sum of the singular values; reason: the same quantity, written without a square root of an operator
--   - encoding: F^st_t(ν) = Tr[M_t(ν)²] → framePotential ν t = Re Tr[M_t(ν)²]; reason: M_t(ν) is Hermitian, so the trace is real
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), proof of Corollary 4.17, p.44

import Mathlib
import Definitions.Def_DesignTest_momentDist
import Definitions.Def_DesignTest_IsMUBFamily

set_option autoImplicit false

namespace DesignTest

open MeasureTheory

/-- **Uniform exact designs for `t = 1, 2`** (proof of Corollary 4.17). A. Kawachi, Y. Nakata, Y. Takeuchi,
*Testing State and Unitary Designs*, STOC 2027 submission (sha256 e2f0a429…), proof of Corollary 4.17,
p.44.
1. For `d ≥ 2`, the uniform measure on an orthonormal basis of `ℂ^d` is an exact state `1`-design.
2. For `d ≥ 2`, the uniform measure `ν₀` on the `L = d(d + 1)` vectors of a complete set of `d + 1`
   pairwise mutually unbiased orthonormal bases has `F^st_2(ν₀) = 1/D_Sym` and is an exact state
   `2`-design.

**Formalization Note.** Clause 2 is stated for every `d` that admits such a family; the paper takes `d` a
prime power, where the family exists by [WF89] (the milestone `mub_exists_prime_power`). -/
theorem uniform_designs_t1_t2 :
    (∀ d : ℕ, 2 ≤ d → ∀ b : Fin d → PureVec d,
        Orthonormal ℂ (fun i => ((b i : PureVec d) : EuclideanSpace ℂ (Fin d))) →
        momentDist 1 (haarState d) (unifList b) = 0) ∧
      ∀ d : ℕ, 2 ≤ d → ∀ B : Fin (d + 1) → Fin d → PureVec d, IsMUBFamily B →
        framePotential (unifList fun p : Fin (d + 1) × Fin d => B p.1 p.2) 2 = 1 / (DSym d 2 : ℝ) ∧
          momentDist 2 (haarState d) (unifList fun p : Fin (d + 1) × Fin d => B p.1 p.2) = 0 := by sorry

end DesignTest
