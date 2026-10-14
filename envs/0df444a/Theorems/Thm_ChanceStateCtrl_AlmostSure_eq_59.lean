-- Prove2me | Theorems.Thm_ChanceStateCtrl_AlmostSure_eq_59
-- name    : ChanceStateCtrl.AlmostSure.eq_59
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:09:30.958676+00:00
-- url     : https://prove2.me/theorems/098873c7-ec30-4266-b400-d3824f1b54fd
-- title:
--   (59), p. 22 — λ(·, ω) ≥ 0 a.s., the split complementarity (59), and ⟨λ(·, ω), y*(·, ω) − α⟩ = 0 a.s.
-- statement:
--   Let $\lambda^*=\lambda^a+\lambda^\circ\in(L^\infty_{\mathbb P}(\Omega,\mathcal C(\bar D)))^*$ with $\lambda^\circ$ singular and $\lambda^a$ represented by $\lambda\in\Lambda_1(\mathcal C(\bar D)^*)$, and suppose (57) holds: $\langle\lambda^\circ,y\rangle\le0$ and $\mathbb E[\langle\lambda,y\rangle]\le0$ for all $y\in\mathcal K$. Let $u^*\in L^2(D)$ with $\mathcal G(u^*)=y^*-\boldsymbol\alpha\in\mathcal K$ and $\langle\lambda^*,\mathcal G(u^*)\rangle=0$. Then
--
--   1. $\lambda(\cdot,\omega)\ge0$ $\mathbb P$-a.s., i.e. $\langle\lambda(\omega),\varphi\rangle\ge0$ for every nonnegative $\varphi\in\mathcal C(\bar D)$, for $\mathbb P$-a.e. $\omega$ (one null set for all $\varphi$);
--   2. (59) holds:
--   $$\langle\lambda^\circ,y^*-\boldsymbol\alpha\rangle=0\qquad\text{and}\qquad\langle\lambda^a,y^*-\boldsymbol\alpha\rangle=\mathbb E[\langle\lambda,y^*-\boldsymbol\alpha\rangle]=0;$$
--   3. $\langle\lambda(\cdot,\omega),y^*(\cdot,\omega)-\boldsymbol\alpha\rangle=0$ $\mathbb P$-a.s.
--
--   These are the sign and complementarity conditions (56c)–(56d) of Theorem 3.10.
--
--   **Formalization Note** $y^*-\boldsymbol\alpha$ is written $\mathcal G(u^*)$ (`Gop P Ainv ftil α us`), with $A^{-1}$ any continuous linear map; the PDE is not used.
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, p. 22, proof of Theorem 3.10, from "To conclude" to the end, (59)

import Mathlib
import Definitions.Def_ChanceStateCtrl_AlmostSure_Setting

open MeasureTheory

namespace ChanceStateCtrl.AlmostSure

/-- Proof of Theorem 3.10, p. 22, from (57) to the end. Let `λ* = λᵃ + λ°` with `λᵃ` represented
by `λ ∈ Λ₁(C(D̄)*)`, and suppose (57): `⟨λ°, y⟩ ≤ 0` and `𝔼[⟨λ, y⟩] ≤ 0` for all `y ∈ 𝒦`. If
`𝒢(u*) = y* − 𝛂 ∈ 𝒦` and `⟨λ*, 𝒢(u*)⟩ = 0`, then (a) `λ(·, ω) ≥ 0` (as a functional on `C(D̄)`)
`P`-a.s.; (b) (59): `⟨λ°, y* − 𝛂⟩ = 0` and `⟨λᵃ, y* − 𝛂⟩ = 𝔼[⟨λ, y* − 𝛂⟩] = 0`; and
(c) `⟨λ(·, ω), y*(·, ω) − 𝛂⟩ = 0` `P`-a.s. -/
theorem eq_59 {d : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace (closure D)]
    (Ainv : ChanceStateCtrl.PDE.L2 D →L[ℝ] C(closure D, ℝ))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ftil : Lp (ChanceStateCtrl.PDE.L2 D) ⊤ P) (α : ℝ) (us : ChanceStateCtrl.PDE.L2 D)
    (lamStar lamA lamSing : StrongDual ℝ (Linf D P)) (lam : Ω → StrongDual ℝ C(closure D, ℝ))
    (hlam : lam ∈ Lambda1 C(closure D, ℝ) P)
    (hrep : ∀ y : Linf D P, lamA y = ∫ ω, lam ω (y ω) ∂P)
    (hsing : IsSingular P lamSing) (hsplit : lamStar = lamA + lamSing)
    (h57 : ∀ y ∈ Kcone D P, lamSing y ≤ 0 ∧ ∫ ω, lam ω (y ω) ∂P ≤ 0)
    (hfeas : Gop P Ainv ftil α us ∈ Kcone D P) (hcompl : lamStar (Gop P Ainv ftil α us) = 0) :
    -- (a) `λ(·, ω) ≥ 0`, `P`-a.s.
    (∀ᵐ ω ∂P, ∀ φ : C(closure D, ℝ), (∀ x, 0 ≤ φ x) → 0 ≤ lam ω φ) ∧
    -- (b) (59)
    (lamSing (Gop P Ainv ftil α us) = 0 ∧ lamA (Gop P Ainv ftil α us) = 0 ∧
      ∫ ω, lam ω (Gop P Ainv ftil α us ω) ∂P = 0) ∧
    -- (c) pointwise complementarity
    (∀ᵐ ω ∂P, lam ω (Gop P Ainv ftil α us ω) = 0) := by sorry

end ChanceStateCtrl.AlmostSure
