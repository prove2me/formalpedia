-- Prove2me | Theorems.Thm_EndoRefLA_PartialPPE_theorem_3
-- name    : EndoRefLA.PartialPPE.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:22:58.892849+00:00
-- url     : https://prove2.me/theorems/588be8f8-1444-4317-bb36-58c994ad26b9
-- title:
--   Theorem 3, p. 19 — the partially endogenous PPE is X*_ex(λ), X*_ex(1) = X*_en, or X*_ex(Λpe(c0)) with Λpe(c0) ∈ (1, λ∧λmax) strictly decreasing in c0
-- statement:
--   Throughout, $(\Omega,\mathcal F,P)$ is a probability space; the pricing kernel $\rho$ is a positive, integrable random variable; the initial wealth is $x_0>0$; the gain-loss weight is $\alpha>0$; the intrinsic degree of loss aversion is $\lambda\ge 1$; the utility $u$ satisfies Assumption 1; and the exogenous reference point $B_0\ge 0$ is measurable with $\mathbb E|u(B_0)|<\infty$.
--   Deviating from $B_0$ costs $f_{B_0}(V_\lambda(X\mid B_0))$, where $f_{B_0}:\mathbb R\to\mathbb R$ is strictly decreasing and continuous. An agent who bears at most $c_0$ chooses from $\mathcal Y(B_0,c_0)$ of (9). The partially endogenous PPE $X^*_{\rm pe}(\lambda,c_0)$ is a PE within $\mathcal Y(B_0,c_0)$ that maximizes $V_\lambda(X\mid X)$ among such PEs (problem (10)).
--
--   Let $\nu_G,\nu_L$ satisfy their root equations and $\lambda_{\max}$ be given by (6). For each $\Lambda\ge1$, let $X^*_{\rm ex}(\Lambda)$ be an optimal solution of (4) with degree of loss aversion $\Lambda$. Put
--   $$\underline c=f_{B_0}\big(V_\lambda(X^*_{\rm ex}(\lambda)\mid B_0)\big),\qquad \bar c=f_{B_0}\big(V_\lambda(X^*_{\rm ex}(1)\mid B_0)\big).$$
--   Then:
--   1. If $c_0=\underline c$, the partially endogenous PPE exists, is unique, and $X^*_{\rm pe}(\lambda,c_0)=X^*_{\rm ex}(\lambda)=X^*_{\rm ex}(\lambda\wedge\lambda_{\max})$.
--   2. If $c_0\ge\bar c$, the partially endogenous PPE exists, is unique, and $X^*_{\rm pe}(\lambda,c_0)=X^*_{\rm ex}(1)=X^*_{\rm en}$, where $X^*_{\rm en}=(u')^{-1}(\nu\rho)$ with $\mathbb E[\rho X^*_{\rm en}]=x_0$.
--   3. There is a function $\Lambda_{\rm pe}$ with the following properties for $\underline c<c_0<\bar c$:
--      - $\Lambda_{\rm pe}(c_0)\in(1,\lambda\wedge\lambda_{\max})$ is the unique $\Lambda$ in that interval with $f_{B_0}(V_\lambda(X^*_{\rm ex}(\Lambda)\mid B_0))=c_0$;
--      - the partially endogenous PPE exists, is unique, and equals $X^*_{\rm ex}(\Lambda_{\rm pe}(c_0))$;
--      - $\Lambda_{\rm pe}$ is strictly decreasing and continuous on $(\underline c,\bar c)$, and
--   $$\lim_{c_0\downarrow\underline c}\Lambda_{\rm pe}(c_0)=\lambda\wedge\lambda_{\max},\qquad\lim_{c_0\uparrow\bar c}\Lambda_{\rm pe}(c_0)=1.$$
--
--   Partial endogenization of the reference point therefore acts exactly like a reduction of loss aversion. The exhibited degree of loss aversion decreases from the intrinsic level (capped at $\lambda_{\max}$) to $1$ as the agent's tolerance for mental cost grows.
--
--   **Formalization Note.** "$X^*_{\rm pe}(\lambda,c_0)=X$" is rendered as: a prospect is a partially endogenous PPE if and only if it is measurable, nonnegative, affordable and a.s. equal to $X$. This gives both existence and a.s. uniqueness. The standing condition $c_0\ge\underline c$ (p. 18) is built into the three cases. The second limit is printed $c_0\uparrow\underline c$; the domain $(\underline c,\bar c)$ and the proof (p. 34) show it is $c_0\uparrow\bar c$, which is stated here. A prospect with $V_\lambda(X\mid B_0)=-\infty$ is not in $\mathcal Y(B_0,c_0)$, because the domain of $f_{B_0}$ is not stated. A PE candidate is an admissible reference point, $\mathbb E|u(X)|<\infty$. The family $X^*_{\rm ex}(\cdot)$ and the multipliers $\nu_G,\nu_L$ are taken as hypotheses; Theorem 1 and Proposition 1 show that they exist and are unique.
-- source:
--   He & Strub, How Endogenization of the Reference Point Affects Loss Aversion: A Study of Portfolio Selection, SSRN 3318295 (version of May 4, 2022), p. 19 (PDF 19), Theorem 3; the second limit of (iii) corrected to c0 ↑ c̄ per its proof, p. 34

import Mathlib
import Definitions.Def_EndoRefLA_PartialPPE_Model

namespace EndoRefLA.PartialPPE

open MeasureTheory Filter Topology

/-- **Theorem 3**, p. 19: the partially endogenous PPE given `Y(B0, c0)`, with
`c̲ = f_B0(V_λ(X*_ex(λ)|B0))` and `c̄ = f_B0(V_λ(X*_ex(1)|B0))`. The second limit of (iii) is
`c0 ↑ c̄` (printed `c0 ↑ c̲`; corrected per the proof, p. 34). -/
theorem theorem_3
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ρ : Ω → ℝ) (x0 α lam : ℝ) (u : ℝ → ℝ) (u0 : EReal) (B0 : Ω → ℝ)
    (hρ : IsPricingKernel P ρ) (hx0 : 0 < x0) (hα : 0 < α) (hlam : 1 ≤ lam)
    (hu : Assumption1 P ρ u u0) (hB0 : IsRefPoint P u u0 B0)
    (f : ℝ → ℝ) (hf : StrictAnti f) (hfc : Continuous f)
    (νG νL : ℝ)
    (hνG : price P ρ B0 < ENNReal.ofReal x0 →
      0 < νG ∧ price P ρ (fun ω => max (Iinv u (νG * ρ ω)) (B0 ω)) = ENNReal.ofReal x0)
    (hνL : ENNReal.ofReal x0 < price P ρ B0 →
      0 < νL ∧ price P ρ (fun ω => min (Iinv u (νL * ρ ω)) (B0 ω)) = ENNReal.ofReal x0)
    (Xex : ℝ → Ω → ℝ) (hXex : ∀ Λ : ℝ, 1 ≤ Λ → IsOptEx P ρ x0 α u u0 B0 Λ (Xex Λ)) :
    -- (i) c0 = c̲
    (∀ X : Ω → ℝ, IsPPEin P α u u0 lam (Ycal P ρ x0 α u u0 lam B0 f (f (V P α u u0 lam (Xex lam) B0).toReal)) X ↔
      (Feasible P ρ x0 X ∧ X =ᵐ[P] Xex lam)) ∧
    Xex (lamCap P ρ x0 α lam u B0 νG νL) =ᵐ[P] Xex lam ∧
    -- (ii) c0 ≥ c̄
    (∀ c0 : ℝ, f (V P α u u0 lam (Xex 1) B0).toReal ≤ c0 → ∀ X : Ω → ℝ,
      IsPPEin P α u u0 lam (Ycal P ρ x0 α u u0 lam B0 f c0) X ↔ (Feasible P ρ x0 X ∧ X =ᵐ[P] Xex 1)) ∧
    (∃ ν : ℝ, 0 < ν ∧ price P ρ (fun ω => Iinv u (ν * ρ ω)) = ENNReal.ofReal x0) ∧
    (∀ ν : ℝ, 0 < ν → price P ρ (fun ω => Iinv u (ν * ρ ω)) = ENNReal.ofReal x0 →
      Xex 1 =ᵐ[P] fun ω => Iinv u (ν * ρ ω)) ∧
    -- (iii) c̲ < c0 < c̄
    ∃ Λpe : ℝ → ℝ,
      (∀ c0 ∈ Set.Ioo (f (V P α u u0 lam (Xex lam) B0).toReal) (f (V P α u u0 lam (Xex 1) B0).toReal),
        Λpe c0 ∈ Set.Ioo 1 (lamCap P ρ x0 α lam u B0 νG νL) ∧
        f (V P α u u0 lam (Xex (Λpe c0)) B0).toReal = c0 ∧
        (∀ Λ ∈ Set.Ioo 1 (lamCap P ρ x0 α lam u B0 νG νL), f (V P α u u0 lam (Xex Λ) B0).toReal = c0 → Λ = Λpe c0) ∧
        ∀ X : Ω → ℝ, IsPPEin P α u u0 lam (Ycal P ρ x0 α u u0 lam B0 f c0) X ↔
          (Feasible P ρ x0 X ∧ X =ᵐ[P] Xex (Λpe c0))) ∧
      StrictAntiOn Λpe (Set.Ioo (f (V P α u u0 lam (Xex lam) B0).toReal) (f (V P α u u0 lam (Xex 1) B0).toReal)) ∧
      ContinuousOn Λpe (Set.Ioo (f (V P α u u0 lam (Xex lam) B0).toReal) (f (V P α u u0 lam (Xex 1) B0).toReal)) ∧
      Tendsto Λpe (𝓝[>] (f (V P α u u0 lam (Xex lam) B0).toReal)) (𝓝 (lamCap P ρ x0 α lam u B0 νG νL)) ∧
      Tendsto Λpe (𝓝[<] (f (V P α u u0 lam (Xex 1) B0).toReal)) (𝓝 1) := by sorry

end EndoRefLA.PartialPPE
