-- Prove2me | Theorems.Thm_BenignDegen_lemma_F_1
-- name    : BenignDegen.lemma_F_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:57:03.683209+00:00
-- url     : https://prove2.me/theorems/e125fbaf-3c41-4fb6-97d9-ba6e4b4540a9
-- title:
--   Lemma F.1 — a setwise error bound plus averagedness gives eventual Q-linear contraction and R-linear convergence
-- statement:
--   Let $E$ be a finite-dimensional real inner product space and $\|\cdot\|_G$ the norm of a symmetric operator $G$ with $g_{\min}\|z\|^2\le\|z\|_G^2\le g_{\max}\|z\|^2$, $0<g_{\min}\le g_{\max}$. Let $T$ be $\alpha$-averaged in $\|\cdot\|_G$, $0<\alpha<1$, with $\operatorname{Fix}T\ne\emptyset$, and suppose
--
--   $$
--   \|Tz-z\|\ge c\operatorname{dist}(z,\operatorname{Fix}T)\quad\text{whenever}\quad\operatorname{dist}(z,\operatorname{Fix}T)\le t_0 .
--   $$
--
--   Then every orbit $z^{k+1}=T(z^k)$ converges to a point of $\operatorname{Fix}T$; it eventually enters the error-bound neighborhood, after which $\operatorname{dist}_G(z^k,\operatorname{Fix}T)$ contracts Q-linearly, and the iterates converge R-linearly.
--
--   Differences from the source:
--   - encoding: R-linear convergence, eventual Q-linear contraction → RLinearTo (‖u_k − ū‖ ≤ cρ^k for all k, 0 ≤ ρ < 1), EventuallyQLinear (d_{k+1} ≤ ρ d_k for all k ≥ K, 0 ≤ ρ < 1); reason: the standard definitions; ρ < 1 is strict
--   - encoding: a norm ‖·‖_G → ‖z‖_G² = ⟨z, Gz⟩ for a linear G with ⟨Gu, v⟩ = ⟨u, Gv⟩; reason: the metric norms of the paper (G_τ, G_P) are of this form; with the two-sided bound G is positive definite
--   - reading: constants c, t₀ of the error-bound hypothesis (sign not printed) → c > 0, t₀ > 0; reason: the lemma is applied with the positive constants of (3.9); for c ≤ 0 the hypothesis is void and no rate can follow
-- source:
--   Kang, Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations, arXiv:2610.20270v1, Appendix F.1, Lemma F.1, p.27

import Mathlib
import Definitions.Def_BenignDegen_SDP
import Definitions.Def_BenignDegen_Geometry
import Definitions.Def_BenignDegen_Convergence
import Definitions.Def_BenignDegen_Algorithms
import Definitions.Def_BenignDegen_Boolean
open SunNLSDP.Equiv Matrix Filter Topology
open scoped RealInnerProductSpace Pointwise

namespace BenignDegen

/-- Lemma F.1 (setwise error bound plus averagedness), Kang, *Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations*, arXiv:2610.20270v1, p.27.
Let `T` be `α`-averaged, `0 < α < 1`, in a norm `‖·‖_G` with `g_min‖·‖² ≤ ‖·‖²_G ≤ g_max‖·‖²`,
`0 < g_min ≤ g_max`, on a finite-dimensional space; suppose `Fix T ≠ ∅` and
`‖Tz − z‖ ≥ c dist(z, Fix T)` whenever `dist(z, Fix T) ≤ t₀`. Then every orbit converges to a
point of `Fix T`; it eventually enters the error-bound neighborhood, after which
`dist_G(z^k, Fix T)` contracts Q-linearly, and the iterates converge R-linearly.

**Formalization Note** `‖·‖_G` is the norm of a symmetric operator `G` (`‖z‖²_G = ⟨z, Gz⟩`);
the constants `c, t₀` are positive, as in the paper's use. -/
theorem lemma_F_1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (G : E →L[ℝ] E) (hG : ∀ u v : E, ⟪G u, v⟫ = ⟪u, G v⟫)
    (gmin gmax : ℝ) (hgmin : 0 < gmin) (hgle : gmin ≤ gmax)
    (hbd : ∀ z : E, gmin * ‖z‖ ^ 2 ≤ gSq G z ∧ gSq G z ≤ gmax * ‖z‖ ^ 2)
    (α : ℝ) (T : E → E) (hT : IsAveragedIn G α T) (hfix : (fixedPts T).Nonempty)
    (c t0 : ℝ) (hc : 0 < c) (ht0 : 0 < t0)
    (heb : ∀ z : E, Metric.infDist z (fixedPts T) ≤ t0 →
      c * Metric.infDist z (fixedPts T) ≤ ‖T z - z‖)
    (z : ℕ → E) (hz : ∀ k, z (k + 1) = T (z k)) :
    ∃ zbar ∈ fixedPts T, Tendsto z atTop (𝓝 zbar) ∧
      (∃ K : ℕ, (∀ k ≥ K, Metric.infDist (z k) (fixedPts T) ≤ t0) ∧
        ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧
          ∀ k ≥ K, gDist G (z (k + 1)) (fixedPts T) ≤ ρ * gDist G (z k) (fixedPts T)) ∧
      RLinearTo z zbar := by sorry

end BenignDegen
