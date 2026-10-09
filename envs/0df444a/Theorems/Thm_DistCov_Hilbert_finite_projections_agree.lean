-- Prove2me | Theorems.Thm_DistCov_Hilbert_finite_projections_agree
-- name    : DistCov.Hilbert.finite_projections_agree
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:28:04.777466+00:00
-- url     : https://prove2.me/theorems/949b28af-f0f8-414e-a417-ab59640b8b8d
-- title:
--   p. 19 — the ε-approximation: µ₁[⟨u≤L, v⟩ ≤ s] = µ₂[⟨u≤L, v⟩ ≤ s] for all L, v ∈ ℝᴸ, s
-- statement:
--   Let $\mu_1,\mu_2$ be Borel probability measures on $\ell^2(\mathbb Z^+)$ with finite first moments, and let $F=\beta(\mu_1-\mu_2)$ be as above:
--   $$F(w,s)=\mu_1\{u\,;\,w(u)\le cs\}-\mu_2\{u\,;\,w(u)\le cs\}.$$
--   Suppose that for every $K\ge0$, for $\rho$-a.e. $w$, $F((v,w),s)=0$ for all $v\in\mathbb R^K$ and $s\in\mathbb R$. Then for every $L$, every $v\in\mathbb R^L$ and every $s\in\mathbb R$,
--   $$\mu_1\big[\langle u_{\le L},v\rangle\le s\big]=\mu_2\big[\langle u_{\le L},v\rangle\le s\big],$$
--   where $u_{\le L}=(u_1,\dots,u_L)$.
--
--   This is the conclusion of the last paragraph of the proof of Theorem 3.16; together with the Cramér–Wold reduction it yields $\mu_1=\mu_2$.
--
--   **Formalization Note.** Indices start at $0$, so $u_{\le L}$ is $(u_0,\dots,u_{L-1})$. The hypothesis "for every $K$" stands in for the paper's choice of $K$ large enough for a given $\epsilon$.
-- source:
--   Lyons, Distance covariance in metric spaces, arXiv:1106.5758 (version of 19 Dec. 2020), p. 19, proof of Theorem 3.16, last paragraph

import Mathlib
import Definitions.Def_DistCov_Hilbert_Setting

namespace DistCov.Hilbert

open MeasureTheory ProbabilityTheory

theorem finite_projections_agree (μ₁ μ₂ : Measure DistCov.Indep.L2N) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (h₁ : DistCov.Indep.FiniteFirstMoment μ₁) (h₂ : DistCov.Indep.FiniteFirstMoment μ₂)
    (h : ∀ K : ℕ, ∀ᵐ w ∂rho, ∀ (v : Fin K → ℝ) (s : ℝ), baryDiff μ₁ μ₂ (splice K v w, s) = 0) :
    ∀ (L : ℕ) (v : Fin L → ℝ) (s : ℝ),
      μ₁ {u : DistCov.Indep.L2N | ∑ i : Fin L, u i * v i ≤ s} = μ₂ {u : DistCov.Indep.L2N | ∑ i : Fin L, u i * v i ≤ s} := by sorry

end DistCov.Hilbert
