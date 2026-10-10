-- Prove2me | Theorems.Thm_BayesRouting_VOI_eqPotential_convex_dirDeriv
-- name    : BayesRouting.VOI.eqPotential_convex_dirDeriv
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T15:09:55.735813+00:00
-- url     : https://prove2.me/theorems/cf954c64-84b8-4fcf-9b45-1eb6855767f2
-- title:
--   Lemma 5 — $\Psi$ is convex and $V^{ij*}(\lambda)=-\frac1D\nabla_{z^{ij}}\Psi(\lambda)$
-- statement:
--   The equilibrium potential value $\Psi(\lambda)=\min_{q\in\mathcal Q(\lambda)}\Phi(q)$ is convex on the simplex of size vectors. It is directionally differentiable: for every $\lambda$ in the simplex and every direction $d$ with $\lambda+\delta d$ in the simplex for some $\delta>0$, the limit $\lim_{\varepsilon\to0^+}(\Psi(\lambda+\varepsilon d)-\Psi(\lambda))/\varepsilon$ exists and is finite. Moreover, let $i\ne j$ and let $\lambda$ be in the simplex with $\lambda^j>0$. For every BWE $q$ of $\Gamma(\lambda)$ the one-sided directional derivative
--
--   $$\nabla_{z^{ij}}\Psi(\lambda)=\lim_{\varepsilon\to0^+}\frac{\Psi(\lambda+\varepsilon z^{ij})-\Psi(\lambda)}{\varepsilon}$$
--
--   exists and
--
--   $$V^{ij*}(\lambda)=-\frac1D\nabla_{z^{ij}}\Psi(\lambda),$$
--
--   where $V^{ij*}(\lambda)=C^{j*}(\lambda)-C^{i*}(\lambda)$ is evaluated at $q$.
--
--   This identity converts statements about the monotonicity of $\Psi$ along $z^{ij}$ into the sign of the relative value of information.
--
--   **Formalization Note** The limit is stated as convergence of the difference quotient to $-D\,V^{ij*}(\lambda)$. The hypothesis $\lambda^j>0$ is **added**: if $\lambda^j=0$ then $\lambda+\varepsilon z^{ij}$ leaves the simplex for every $\varepsilon>0$, where $\Psi$ has no meaning. $\lambda^i=0$ is allowed. Directional differentiability is stated for every direction that keeps $\lambda$ in the simplex (the domain of $\Psi$).
-- source:
--   Wu, Amin, Ozdaglar, Value of Information in Bayesian Routing Games, Oper. Res. 69(1) 2021, p. 158, Lemma 5, eq. (26)

import Mathlib
import Definitions.Def_BayesRouting_VOI_Game
import Definitions.Def_BayesRouting_VOI_Potential
import Definitions.Def_BayesRouting_VOI_Flows
import Definitions.Def_BayesRouting_VOI_Pairwise

open Filter Topology

namespace BayesRouting.VOI

/-- **Lemma 5** (Wu, Amin, Ozdaglar, Oper. Res. 69(1) 2021, p. 158). `Ψ` is convex on the simplex;
it is directionally differentiable in `λ`: at every `λ` in the simplex and in every direction `d`
along which `λ` can move while staying in the simplex, the one-sided derivative
`lim_{ε→0⁺} (Ψ(λ + ε d) - Ψ(λ)) / ε` exists (as a real number); and for distinct populations `i, j`, a size vector `λ` in the simplex
with `λ^j > 0` and every BWE `q` of `Γ(λ)`, the one-sided derivative of `Ψ` at `λ` in the direction `z^{ij}` exists and equals
`-D V^{ij*}(λ)`, i.e. `V^{ij*}(λ) = -(1/D) ∇_{z^{ij}} Ψ(λ)` (26). The hypothesis `λ^j > 0` is added:
for `λ^j = 0` the point `λ + ε z^{ij}` leaves the simplex for every `ε > 0`. -/
theorem eqPotential_convex_dirDeriv {I : Type} [Fintype I] [DecidableEq I] {T : I → Type} [∀ i, Fintype (T i)]
    [∀ i, DecidableEq (T i)] [∀ i, Nonempty (T i)] {S E R : Type} [Fintype S] [Fintype E]
    [DecidableEq E] [Fintype R] [Nonempty R]
    (G : Game I T S E R) :
    ConvexOn ℝ (stdSimplex ℝ I) (eqPotential G) ∧
      (∀ lam ∈ stdSimplex ℝ I, ∀ d : I → ℝ, (∃ δ : ℝ, 0 < δ ∧ lam + δ • d ∈ stdSimplex ℝ I) →
        ∃ L : ℝ, Tendsto (fun ε : ℝ => (eqPotential G (lam + ε • d) - eqPotential G lam) / ε)
          (𝓝[>] 0) (𝓝 L)) ∧
      ∀ lam ∈ stdSimplex ℝ I, ∀ i j : I, i ≠ j → 0 < lam j →
        ∀ q : (k : I) → T k → R → ℝ, IsBWE G lam q →
          Tendsto (fun ε : ℝ => (eqPotential G (lam + ε • dir i j) - eqPotential G lam) / ε)
            (𝓝[>] 0) (𝓝 (-(G.D * relValue G q i j))) := by sorry

end BayesRouting.VOI
