-- Prove2me | Theorems.Thm_DynkinAsymInfo_Linear_theorem_5_1
-- name    : DynkinAsymInfo.Linear.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:18:19.572777+00:00
-- url     : https://prove2.me/theorems/def56f84-c8ea-4b24-8258-2519449df511
-- title:
--   Theorem 5.1 — quasi-variational verification
-- statement:
--   In the §6 GBM model, let $u^0,u^1\ge0$ be continuous candidate values and $u=u^0+\phi u^1$. Define continuation sets $C=\{u>(1+\phi)f\}$ and $C^i=\{u^i<g\}$ in $(0,\infty)^2$, and their complementary stopping sets $S,S^i$. Assume the regularity and quasi-variational conditions (42)–(45): $u$ is locally $W^{2,\infty}$ on $C^0\cap C^1$, $C^1$ on its relative closure and $C^2$ on the relative closure of $C\cap C^0\cap C^1$; each $u^i$ is $C^2$ there; the type generators vanish in the joint continuation region, $u^i\le g$, $u^i=f$ on $S$, and each $\partial_\phi u^i=0$ on $S^0\cup S^1$.
--
--   Suppose an admissible pair of type controls stays strictly below one under both conditional laws, has disjoint jumps, keeps $(X,\Phi^*)$ in the relative closure of $C^0\cap C^1$, and satisfies the support and jump-crossing conditions (46)–(48). If the first exit $\tau^*$ from $C$ is almost surely finite and the two transversality limits (49) hold for both types and both localisation sequences, then the induced pair is a saddle point and
--   $$\widehat J(\tau^*,\Gamma^*)=u(x,\phi),\qquad J^i(\tau^*,\Gamma^{*,i})=u^i(x,\phi)\quad(i=0,1).$$
--   This is the verification result used to certify the explicit equilibrium of Theorem 6.10.
--
--   **Formalization Note.** The source's general diffusion is specialised to the GBM instance; $f,g$ remain general. Relative closures, a.e. equation (42), left limits, the jump at zero, and the printed localisation integral are explicit. The source's $v=u=\widehat J$ in (50) uses a scaled value: the ex-ante value is $u/(1+\phi)$.
-- source:
--   De Angelis, Ekström, Glover, Dynkin Games with Incomplete and Asymmetric Information, arXiv:1810.07674v5, pp. 13–14, Theorem 5.1, (40)–(50)

import Mathlib
import Definitions.Def_DynkinAsymInfo_Linear_QVI

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace DynkinAsymInfo.Linear
set_option autoImplicit false

/-- De Angelis, Ekström, Glover, *Dynkin Games with Incomplete and Asymmetric Information*,
arXiv:1810.07674v5, pp. 13–14, Theorem 5.1 (GBM instance). A sufficiently regular
solution of (42)–(45) and a control satisfying (46)–(49) give a saddle point
and the scaled and interim payoffs (50).

**Formalization Note.** The closure is relative to `(0,∞)²`. Local `W^{2,∞}`
is represented by `C¹` with locally Lipschitz first derivative on the open
region. Equation (42) is Lebesgue-a.e. there. The full GBM generators include
the factors of x. The printed `I(h)` has only one factor of `Φ*` in its second
summand. Left limits at zero use `Φ*_{0-}=ϕ` and `Γ_{0-}=0`; the support
conditions count an initial jump explicitly. The source's `v=u=Ĵ` in (50)
is read as `(1+ϕ)v=u=Ĵ`, so only the two payoff identities are asserted here.
The transversality limits are imposed at this starting point. -/
theorem theorem_5_1 {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (x phi : ℝ) (hx : 0 < x) (hphi : 0 < phi)
    (f g : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi 0)) (hg : ContinuousOn g (Set.Ioi 0))
    (hfg : ∀ y, 0 < y → 0 ≤ f y ∧ f y ≤ g y)
    (u0 u1 : ℝ × ℝ → ℝ)
    (hu0 : ContinuousOn u0 stateDomain) (hu1 : ContinuousOn u1 stateDomain)
    (hupos : ∀ q ∈ stateDomain, 0 ≤ u0 q ∧ 0 ≤ u1 q)
    (G0 G1 : ℝ≥0 → Ω → ℝ) :
    let pi := phi / (1 + phi)
    let u := combinedValue u0 u1
    let C0 := Ci u0 g
    let C1 := Ci u1 g
    let CC := C u f
    let O := C0 ∩ C1
    let K := relativeClosure (CC ∩ O)
    let taus := exitTime p st x pi G0 G1 u f
    ContDiffOn ℝ 1 u O →
    LocallyLipschitzOn O (fderiv ℝ u) →
    ContDiffOn ℝ 1 u (relativeClosure O) →
    ContDiffOn ℝ 2 u K →
    ContDiffOn ℝ 2 u0 K → ContDiffOn ℝ 2 u1 K →
    (∀ᵐ q ∂(volume.restrict O), max (L0 p u q) ((1 + q.2) * f q.1 - u q) = 0) →
    (∀ q ∈ CC ∩ O, L0 p u0 q = 0 ∧ L1 p u1 q = 0) →
    (∀ q ∈ stateDomain, u0 q ≤ g q.1 ∧ u1 q ≤ g q.1) →
    (∀ q ∈ S u f, u0 q = f q.1 ∧ u1 q = f q.1) →
    (∀ q ∈ Si u0 g ∪ Si u1 g,
      HasDerivAt (fun z => u0 (q.1,z)) 0 q.2 ∧
      HasDerivAt (fun z => u1 (q.1,z)) 0 q.2) →
    InA st (FX p st x pi) G0 → InA st (FX p st x pi) G1 →
    InA st (FXTheta p st x pi) (mixControl st pi G0 G1) →
    (∀ i ∈ ({0, 1} : Set ℝ), ∀ t,
      Ptype st pi i {a | G0 t a < 1} = 1 ∧
      Ptype st pi i {a | G1 t a < 1} = 1) →
    (∀ i ∈ ({0, 1} : Set ℝ),
      ∀ᵐ a ∂(Ptype st pi i),
        (∀ t, controlJump G0 t a * controlJump G1 t a = 0) ∧
        (∀ t, (X p st x pi t a, PhiStar p st x pi G0 G1 t a) ∈
          relativeClosure O) ∧
        (G0 0 a = 0 ∨
          (X p st x pi 0 a, PhiStarLeft p st x pi G0 G1 0 a) ∈ Si u0 g) ∧
        (G1 0 a = 0 ∨
          (X p st x pi 0 a, PhiStarLeft p st x pi G0 G1 0 a) ∈ Si u1 g) ∧
        (pathStieltjes (fun t => G0 t a)).measure
          {t | (X p st x pi t a, PhiStarLeft p st x pi G0 G1 t a) ∉ Si u0 g} = 0 ∧
        (pathStieltjes (fun t => G1 t a)).measure
          {t | (X p st x pi t a, PhiStarLeft p st x pi G0 G1 t a) ∉ Si u1 g} = 0 ∧
        (∀ t, volume (Set.Ioo
          (min (PhiStarLeft p st x pi G0 G1 t a) (PhiStar p st x pi G0 G1 t a))
          (max (PhiStarLeft p st x pi G0 G1 t a) (PhiStar p st x pi G0 G1 t a)) ∩
          {z | (X p st x pi t a, z) ∉ Si u0 g}) = 0) ∧
        (∀ t, volume (Set.Ioo
          (min (PhiStarLeft p st x pi G0 G1 t a) (PhiStar p st x pi G0 G1 t a))
          (max (PhiStarLeft p st x pi G0 G1 t a) (PhiStar p st x pi G0 G1 t a)) ∩
          {z | (X p st x pi t a, z) ∉ Si u1 g}) = 0)) →
    (∀ᵐ a ∂st.P, taus a ≠ ⊤) →
    (∀ i ∈ ({0, 1} : Set ℝ),
      let ui := if i = 0 then u0 else u1
      Transverse p st x pi i G0 G1 u ui u f ∧
        Transverse p st x pi i G0 G1 u ui ui f) →
    IsSaddle p st x pi f g taus (mixControl st pi G0 G1) ∧
      Jhat p st x pi f g taus (mixControl st pi G0 G1) =
        ENNReal.ofReal (u (x, phi)) ∧
      J0 p st x pi f g taus G0 = ENNReal.ofReal (u0 (x, phi)) ∧
      J1 p st x pi f g taus G1 = ENNReal.ofReal (u1 (x, phi)) := by sorry

end DynkinAsymInfo.Linear
