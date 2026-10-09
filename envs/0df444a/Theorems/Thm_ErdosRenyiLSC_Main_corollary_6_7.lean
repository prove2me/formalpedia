-- Prove2me | Theorems.Thm_ErdosRenyiLSC_Main_corollary_6_7
-- name    : ErdosRenyiLSC.Main.corollary_6_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:19:39.299431+00:00
-- url     : https://prove2.me/theorems/5a1130da-48ca-4ecf-9c52-3af40bb9b4fb
-- title:
--   Corollary 6.7, p. 64 — Σ_{α≠N} |⟨v_α, e⟩|² = O(f^{−2}) with high probability
-- statement:
--   Fix $A_0\ge10$, $C>0$ and $C_0>0$. Suppose $A=H+f|e\rangle\langle e|$ satisfies Definition 2.2 (with constants $A_0$, $C$) and, in addition, $f\le C_0N^{1/2}$. Let $v_1,\dots,v_N$ be an orthonormal eigenbasis of $A$ for the eigenvalues $\mu_1\le\dots\le\mu_N$. Then there are $\nu>0$ and $K>0$ such that with $(\xi,\nu)$-high probability
--   $$\sum_{\alpha\ne N}|\langle v_\alpha,e\rangle|^2\le\frac{K}{f^2},\qquad\text{i.e.}\quad f^2\Bigl(1-\langle v_N,e\rangle^2\Bigr)\le K .$$
--
--   For large $f$ the top eigenvector of $A$ is almost parallel to $e$, so $e$ is almost orthogonal to all other eigenvectors; this is what makes the rank-one perturbation harmless for the matrix entries of $(A-z)^{-1}$ in Section 7.
--
--   **Formalization Note** Since $\sum_\alpha|\langle v_\alpha,e\rangle|^2=\|e\|^2=1$, the sum over $\alpha\ne N$ equals $1-\langle v_N,e\rangle^2$; the bound is stated, multiplied by $f^2$ (because $f=0$ is allowed), for every unit eigenvector $v_N$ of the top eigenvalue $\mu_N$, i.e. for every choice of eigenbasis. $\nu$ is chosen before $a_0$ and the model; $K$ after $a_0$ and before the model (the implicit constant of $O(\cdot)$ may depend on the constants of (2.4), p. 7).
-- source:
--   Erdős, Knowles, Yau and Yin, Spectral statistics of Erdős–Rényi graphs I: Local semicircle law, arXiv:1103.1919v5, p. 64, Corollary 6.7, (6.32)

import Mathlib
import Definitions.Def_ErdosRenyiLSC_Main_Setting
import Definitions.Def_ErdosRenyiLSC_Main_Resolvent

noncomputable section

namespace ErdosRenyiLSC.Main

/-- Corollary 6.7, p. 64: if moreover `f ≤ C₀ N^{1/2}`, then with `(ξ, ν)`-high
probability `Σ_{α ≠ N} |⟨v_α, e⟩|² = O(f^{-2})`. For an orthonormal eigenbasis
`v₁, …, v_N` of `A` with `v_N` a unit eigenvector of the top eigenvalue `μ_N`,
`Σ_{α ≠ N} |⟨v_α, e⟩|² = 1 - ⟨v_N, e⟩²`; the bound is stated for every such `v_N`
in the form `f² · (1 - ⟨v_N, e⟩²) ≤ K`. -/
theorem corollary_6_7 :
    ∀ (A₀ C C₀ : ℝ), 10 ≤ A₀ → 0 < C → 0 < C₀ →
      ∃ ν : ℝ, 0 < ν ∧ ∀ a₀ : ℝ, 0 < a₀ → ∃ K : ℝ, 0 < K ∧
        ∀ {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
          [MeasureTheory.IsProbabilityMeasure P]
          (H : (N : ℕ) → Ω → Matrix (Fin N) (Fin N) ℝ)
          (ξ q f : ℕ → ℝ),
          IsSparseEnsemble P H ξ q a₀ A₀ C →
          (∀ᶠ N in (Filter.atTop : Filter ℕ),
            0 ≤ f N ∧ f N ≤ (N : ℝ) ^ C) →
          (∀ᶠ N in (Filter.atTop : Filter ℕ), f N ≤ C₀ * Real.sqrt (N : ℝ)) →
          HighProb P ξ ν (fun N =>
            {ω | ∀ v : Fin N → ℝ, v ⬝ᵥ v = 1 →
              (deformedMatrix H f N ω).mulVec v =
                eigAsc (deformedMatrix H f N ω) (N - 1) • v →
              f N ^ 2 * (1 - (v ⬝ᵥ eVec N) ^ 2) ≤ K}) := by sorry

end ErdosRenyiLSC.Main
