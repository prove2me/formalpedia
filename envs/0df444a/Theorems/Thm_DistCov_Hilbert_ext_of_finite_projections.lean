-- Prove2me | Theorems.Thm_DistCov_Hilbert_ext_of_finite_projections
-- name    : DistCov.Hilbert.ext_of_finite_projections
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:28:39.756521+00:00
-- url     : https://prove2.me/theorems/41c87de1-c36b-4f30-ac00-3ae8d2bed589
-- title:
--   p. 18 — Cramér–Wold: µ₁{⟨u, v⟩ ≤ s} = µ₂{⟨u, v⟩ ≤ s} for all finitely supported v and all s forces µ₁ = µ₂
-- statement:
--   Let $\mu_1,\mu_2$ be finite Borel measures on $\ell^2(\mathbb Z^+)$. Suppose that for every finitely supported $v\in\mathbb R^\infty$ and every $s\in\mathbb R$,
--   $$\mu_1\{u\,;\,\langle u,v\rangle\le s\}=\mu_2\{u\,;\,\langle u,v\rangle\le s\},\qquad \langle u,v\rangle=\sum_n u_nv_n .$$
--   Then $\mu_1=\mu_2$.
--
--   In the paper, with $\mu=\mu_1-\mu_2$: it suffices to show $\mu\{u\,;\,\langle u,v\rangle\le s\}=0$ for all such $v,s$, since then the finite-dimensional marginals of $\mu$ vanish by the Cramér–Wold device. This is the reduction step in the proof of Theorem 3.16.
--
--   **Formalization Note.** The signed measure $\mu=\mu_1-\mu_2$ is expressed through the pair $(\mu_1,\mu_2)$. A finitely supported $v$ is a finitely supported function $\mathbb N\to\mathbb R$, and $\langle u,v\rangle$ is the finite sum over its support. The statement is made for finite measures; the paper uses it for probability measures.
-- source:
--   Lyons, Distance covariance in metric spaces, arXiv:1106.5758 (version of 19 Dec. 2020), p. 18, proof of Theorem 3.16, sentence 'It suffices to show that µ{u ; ⟨u, v⟩ ≤ s} = 0 …'

import Mathlib
import Definitions.Def_DistCov_Hilbert_Setting

namespace DistCov.Hilbert

open MeasureTheory ProbabilityTheory

theorem ext_of_finite_projections (μ₁ μ₂ : Measure DistCov.Indep.L2N) [IsFiniteMeasure μ₁]
    [IsFiniteMeasure μ₂]
    (h : ∀ (v : ℕ →₀ ℝ) (s : ℝ),
      μ₁ {u : DistCov.Indep.L2N | ∑ i ∈ v.support, u i * v i ≤ s} = μ₂ {u : DistCov.Indep.L2N | ∑ i ∈ v.support, u i * v i ≤ s}) :
    μ₁ = μ₂ := by sorry

end DistCov.Hilbert
