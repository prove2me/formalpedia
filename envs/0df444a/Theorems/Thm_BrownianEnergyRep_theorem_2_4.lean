-- Prove2me | Theorems.Thm_BrownianEnergyRep_theorem_2_4
-- name    : BrownianEnergyRep.theorem_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T07:03:18.729175+00:00
-- url     : https://prove2.me/theorems/a494e5bb-7566-45f5-82b6-5560a2e7c49f
-- title:
--   Theorem 2.4 — Wiener measure on $W(G)$
-- statement:
--   Let $p$ be the heat kernel for a Haar measure $dx$. There is a unique probability measure $\mu$ on $(W(G),\mathcal B)$ with the finite dimensional distributions (2.2). Under $\mu$, the process $g$ starts at $e$ and is a diffusion with generator $\tfrac12\Delta$: for $0\le s<t\le T$ and continuous $f$,
--   $$
--   \mu\big(f(g_t)\,\big|\,\mathcal B_s\big)=\int_Gp_{t-s}(g_s^{-1}h)f(h)\,dh\quad\text{a.s.}
--   $$
--   Moreover, for every $f\in C^\infty(G)$, the process
--   $$
--   M^f_t=f(g_t)-f(g_0)-\frac12\int_0^t\Delta f(g_\tau)\,d\tau
--   $$
--   is a martingale for $\{\mathcal B_t\}$. The measure $\mu$ is the Brownian motion on $G$ on which all the representations are built.
--
--   Differences from the source:
--   - encoding: G a compact connected Lie subgroup of GL_n(ℝ), 𝔤 its tangent space at e, with an Ad_G-invariant inner product → a subgroup with CompactSpace and ConnectedSpace, and a MatrixLieAlgebra structure (E, incl, Ad, bracket); reason: a compact subgroup of GL_n(ℝ) is a closed Lie subgroup, and the structure is determined by 𝔤 and the inner product
--   - encoding: p_t = e^{tΔ/2}δ_e, the fundamental solution of (2.1), for a bi-invariant Haar measure dx → hypotheses IsHeatKernel L m p (p jointly smooth on (0,∞)×G, (2.1) pointwise for t > 0, ∫p_t f dm → f(e) for continuous f) for a Haar measure m, and μ given by IsWienerMeasure m p T μ; reason: these conditions determine p_t for t > 0 (theorem_2_1); (2.2) does not depend on the normalization of m; a Haar measure on a compact group is bi-invariant
--   - encoding: Borel σ-algebra of the uniform metric d_∞ on W(G) → Borel σ-algebra of the compact-open topology; reason: the two topologies agree because G is compact
--   - generalization: M^f is a local martingale → M^f is a martingale; reason: the page's proof shows a martingale, which is also a local martingale
--   - encoding: g a diffusion with generator ½Δ → the Markov property with semigroup given by p; path continuity and g₀ = e hold by the definition of W(G); reason: p generates ½Δ by (2.1)
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, Theorem 2.4, pp.3-4

import Mathlib
import Definitions.Def_BrownianEnergyRep_MatrixLieAlgebra
import Definitions.Def_BrownianEnergyRep_MatrixLieAlgebra_laplacian
import Definitions.Def_BrownianEnergyRep_IsSmoothOnGroup
import Definitions.Def_BrownianEnergyRep_IsHeatKernel
import Definitions.Def_BrownianEnergyRep_WienerGroup
import Definitions.Def_BrownianEnergyRep_IsWienerMeasure
import Definitions.Def_BrownianEnergyRep_canonicalFiltration

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- Theorem 2.4 (arXiv:1511.07378v1, pp.3-4): `μ` exists and is unique; `g` is a Markov diffusion with heat
semigroup; `M^f` of (2.3) is a martingale for smooth `f`.

**Formalization Note** The page says local martingale and its proof shows martingale; this states
the martingale. `g₀ = e` holds for every path of `W(G)`. -/
theorem theorem_2_4 {n : ℕ} (G : Subgroup (GL (Fin n) ℝ)) [CompactSpace ↥G] [ConnectedSpace ↥G]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : MatrixLieAlgebra G E) (T : ℝ) [Fact (0 < T)]
    (m : Measure ↥G) [m.IsHaarMeasure] (p : ℝ → ↥G → ℝ) (hp : IsHeatKernel L m p) :
    (∃! μ, IsWienerMeasure m p T μ) ∧
    ∀ μ, IsWienerMeasure m p T μ →
      (∀ s t, 0 ≤ s → s < t → t ≤ T → ∀ f : ↥G → ℝ, Continuous f →
        μ[fun γ => f (pathAt γ t) | canonicalPast G T s] =ᵐ[μ]
          fun γ => ∫ h, p (t - s) ((pathAt γ s)⁻¹ * h) * f h ∂m) ∧
      ∀ f : ↥G → ℝ, IsSmoothOnGroup f →
        Martingale (fun (t : Icc (0 : ℝ) T) (γ : ↥(WienerGroup G T)) =>
          f (pathAt γ t) - f (pathAt γ 0) -
            (1 / 2) * ∫ τ in (0 : ℝ)..t, L.laplacian f (pathAt γ τ))
          (canonicalFiltration G T) μ := by sorry

end BrownianEnergyRep
