-- Prove2me | Theorems.Thm_ConvexRiskFn_Dual_theorem_2_2
-- name    : ConvexRiskFn.Dual.theorem_2_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T07:53:03.859344+00:00
-- url     : https://prove2.me/theorems/f32c6d43-ca98-476b-b95f-f256f5e6273e
-- title:
--   Theorem 2.2, p. 435 — dual representation (2.6) of a proper lsc convex risk function; (A2), (A3), (A4) read off 𝒜 = dom(ρ*)
-- statement:
--   Let $(\Omega,\mathcal F)$ be a measurable space, $\mathcal X$ a locally convex space of $\mathcal F$-measurable functions $\Omega\to\mathbb R$, and $\mathcal Y$ a linear space of finite signed measures paired with $\mathcal X$ by $\langle\mu,X\rangle=\int_\Omega X\,d\mu$, compatibly with the topology of $\mathcal X$, and satisfying condition (C). Let $\rho:\mathcal X\to\overline{\mathbb R}$ be proper, lower semicontinuous and convex, with conjugate $\rho^*(\mu)=\sup_X\{\langle\mu,X\rangle-\rho(X)\}$ and dual domain $\mathcal A=\operatorname{dom}\rho^*=\{\mu\in\mathcal Y:\rho^*(\mu)<+\infty\}$. Then
--   $$\rho(X)=\sup_{\mu\in\mathcal A}\{\langle\mu,X\rangle-\rho^*(\mu)\}\qquad\forall X\in\mathcal X,\qquad(2.6)$$
--   and moreover
--
--   1. (A2) $\rho$ is monotone ($Y\succeq X\Rightarrow\rho(Y)\ge\rho(X)$) if and only if every $\mu\in\mathcal A$ is a nonnegative measure;
--   2. when $\mathcal X$ contains the constant function $1$ (so that $X+a\in\mathcal X$): (A3) $\rho$ is translation equivariant ($\rho(X+a)=\rho(X)+a$, $a\in\mathbb R$) if and only if $\mu(\Omega)=1$ for every $\mu\in\mathcal A$;
--   3. (A4) $\rho$ is positively homogeneous ($\rho(tX)=t\rho(X)$, $t>0$) if and only if
--   $$\rho(X)=\sup_{\mu\in\mathcal A}\langle\mu,X\rangle\qquad\forall X\in\mathcal X.\qquad(2.7)$$
--
--   The theorem generalizes the dual representations of coherent and convex risk measures (Artzner et al., Delbaen, Föllmer–Schied, Cheridito et al.) to paired locally convex spaces: each axiom of a risk function corresponds to a property of the measures in the dual domain.
--
--   **Formalization Note** Condition (C) is the standing assumption of §2 and is a hypothesis; it is used in (i). Part (ii) is stated for every element $\mathbf 1\in\mathcal X$ that is the constant function $1$, with $X+a$ written $X+a\cdot\mathbf 1$; the other parts do not require $\mathcal X$ to contain constants. Values are in `EReal`, where $r-(+\infty)=-\infty$, so measures outside $\mathcal A$ would contribute $-\infty$ to a supremum.
-- source:
--   Ruszczyński, Shapiro, Optimization of convex risk functions, Math. Oper. Res. 31 (2006), p. 435, Theorem 2.2 (with (2.6), (2.7))

import Mathlib
import Definitions.Def_ConvexRiskFn_Dual_Setting

namespace ConvexRiskFn.Dual

/-- Theorem 2.2, p. 435: let `ρ : 𝒳 → ℝ̄` be proper, lower semicontinuous and convex, and let
`𝒜 = dom(ρ*)`. Then `ρ(X) = sup_{μ ∈ 𝒜} {⟨μ, X⟩ − ρ*(μ)}` for all `X` (2.6), and
(i) (A2) holds iff every `μ ∈ 𝒜` is nonnegative; (ii) (A3) holds iff `μ(Ω) = 1` for every
`μ ∈ 𝒜`; (iii) (A4) holds iff `ρ(X) = sup_{μ ∈ 𝒜} ⟨μ, X⟩` for all `X` (2.7).
Condition (C) is the standing assumption of §2. Part (ii) is stated for every `one ∈ 𝒳` that is
the constant function `1` (needed for (A3) to make sense); parts (2.6), (i), (iii) do not need
constants in `𝒳`. -/
theorem theorem_2_2 {Ω : Type*} [MeasurableSpace Ω] {𝒳 : Type*} [AddCommGroup 𝒳] [Module ℝ 𝒳]
    [TopologicalSpace 𝒳] [IsTopologicalAddGroup 𝒳] [ContinuousSMul ℝ 𝒳] [LocallyConvexSpace ℝ 𝒳]
    (S : PairedSpaces Ω 𝒳) (hC : CondC S)
    (ρ : 𝒳 → EReal) (hp : IsProper ρ) (hlsc : LowerSemicontinuous ρ) (hcvx : A1 ρ) :
    (∀ X, ρ X = ⨆ μ ∈ dualDom S ρ, ((pair μ (S.toFun X) : ℝ) : EReal) - conj S ρ μ) ∧
    (A2 S ρ ↔ ∀ μ ∈ dualDom S ρ, 0 ≤ μ) ∧
    (∀ one : 𝒳, S.toFun one = (fun _ => 1) →
      (A3 one ρ ↔ ∀ μ ∈ dualDom S ρ, μ Set.univ = 1)) ∧
    (A4 ρ ↔ ∀ X, ρ X = ⨆ μ ∈ dualDom S ρ, ((pair μ (S.toFun X) : ℝ) : EReal)) := by sorry
end ConvexRiskFn.Dual
