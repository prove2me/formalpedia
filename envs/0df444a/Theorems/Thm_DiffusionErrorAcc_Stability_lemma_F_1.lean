-- Prove2me | Theorems.Thm_DiffusionErrorAcc_Stability_lemma_F_1
-- name    : DiffusionErrorAcc.Stability.lemma_F_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:59:08.963722+00:00
-- url     : https://prove2.me/theorems/0b960cf9-6c15-4e10-8fc3-c222be707edf
-- title:
--   Lemma F.1 — V realizes perturbation of µ by g iff E_µ[gh] = E_µ⟨V, ∇h⟩ for all h ∈ H¹(µ)
-- statement:
--   Let $\mu=\rho\,dx$ be a distribution on $\mathbb R^d$ (positive $C^1$ density), $g\in L^2(\mu)$ a test statistic and $V\in L^2(\mu;\mathbb R^d)$ a ($C^1$) vector field. The following are equivalent:
--
--   1. $V$ realizes perturbation of $\mu$ by $g$, i.e. $-\nabla\cdot(\mu V)=g\mu$;
--   2. $\mathbb E_\mu[gh]=\mathbb E_\mu\langle V,\nabla h\rangle$ for all $h\in H^1(\mu)$.
--
--   $$-\nabla\cdot(\rho V)=g\rho\ \text{ on }\mathbb R^d\iff\int gh\,d\mu=\int\langle V,\nabla h\rangle\,d\mu\quad\forall h\in H^1(\mu).$$
--   The weak form (2) is how realizability is used in the proofs of Lemmas B.2 and B.3, and it gives the dual expression of the transport energy.
--
--   **Formalization Note.** (1) is `Realizes ρ V g` (pointwise, classical divergence); both integrals in (2) are of $L^1(\mu)$ functions since $g,h\in L^2(\mu)$ and $V,\nabla h\in L^2(\mu;\mathbb R^d)$.
--
--   Differences from the source:
--   - encoding: §2.3: µ has a positive C¹ density; a test statistic g is uniformly continuous and C²; a vector field V is C¹ → hypotheses hρ (IsRegDensity ρ), hgu, hg2, hV1, besides the printed g ∈ L²(µ), V ∈ L²(µ; ℝ^d); reason: standing assumptions as binders; the paper's proof invokes them (Section 2.3) in both directions
--   - reading: H¹(µ) = {h ∈ L²(µ) : ∇h exists, and lies in L²(µ; ℝ^d)} → InH1 ρ h: h ∈ L²(µ), h differentiable on all of ℝ^d, classical gradient in L²(µ; ℝ^d); reason: '∇h exists' read as the classical gradient (the paper works with classical derivatives throughout, §2.3)
-- source:
--   Giapitzakis, Moitra, Risteski, Rohatgi, Error accumulation in reverse diffusion with an imperfect score: beyond path-space analyses, STOC 2027 submission (manuscript sha256 c0118fd2…), p. 35, Lemma F.1

import Mathlib
import Definitions.Def_DiffusionErrorAcc_Stability_TransportEnergy

open MeasureTheory

namespace DiffusionErrorAcc.Stability

/-- Lemma F.1 (p. 35). For every distribution `µ = ρ dx` on `ℝ^d`, test statistic `g ∈ L²(µ)` and
(`C¹`) vector field `V ∈ L²(µ; ℝ^d)`, the following are equivalent:
(1) `V` realizes perturbation of `µ` by `g`, i.e. `−∇ · (µV) = g µ`;
(2) `E_µ[g h] = E_µ ⟨V, ∇h⟩` for all `h ∈ H¹(µ)`. -/
theorem lemma_F_1 {d : ℕ} (hd : 1 ≤ d) (ρ : Rd d → ℝ) (hρ : IsRegDensity ρ)
    (g : Rd d → ℝ) (hgL2 : MemLp g 2 (densMeasure ρ)) (hgu : UniformContinuous g)
    (hg2 : ContDiff ℝ 2 g)
    (V : Rd d → Rd d) (hV1 : ContDiff ℝ 1 V) (hVL2 : MemLp V 2 (densMeasure ρ)) :
    Realizes ρ V g ↔
      ∀ h : Rd d → ℝ, InH1 ρ h →
        ∫ x, g x * h x ∂(densMeasure ρ) = ∫ x, inner ℝ (V x) (gradient h x) ∂(densMeasure ρ) := by sorry

end DiffusionErrorAcc.Stability
