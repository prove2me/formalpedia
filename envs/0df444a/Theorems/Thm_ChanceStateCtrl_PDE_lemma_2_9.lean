-- Prove2me | Theorems.Thm_ChanceStateCtrl_PDE_lemma_2_9
-- name    : ChanceStateCtrl.PDE.lemma_2_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T01:21:38.694009+00:00
-- url     : https://prove2.me/theorems/65a487ad-4d23-49f6-b07c-4be77c2763c1
-- title:
--   Lemma 2.9, p. 9 — g of (24) is jointly convex and globally Lipschitzian; the events of (23d) and of φ coincide and are measurable
-- statement:
--   Throughout, $D\subseteq\mathbb R^d$ ($d\in\{1,2,3\}$) is a nonempty, open, bounded domain of class S, $A^{-1}:L^2(D)\to C(\bar D)$ is the solution operator of the Dirichlet problem $-\Delta y=F$ in $D$, $y=0$ on $\partial D$ (in $H^1_0(D)\cap C(\bar D)$), $f_0,\varphi_1,\dots,\varphi_m\in L^2(D)$, and $S(u,z)=A^{-1}(u+f_0+\sum_i z_i\varphi_i)$, $P(u,z)=A^{-1}u+\sum_i z_iA^{-1}\varphi_i$ are the operators of (5). The constraint function of (24) is $g(u,z)=\max_{x\in\bar D}[S(u,z)](x)-\alpha$ for a threshold $\alpha\in\mathbb R$.
--
--   Let $\xi:\Omega\to\mathbb R^m$ be measurable. Then $g:L^2(D)\times\mathbb R^m\to\mathbb R$ is convex (jointly in both variables) and globally Lipschitzian, and for every $u\in L^2(D)$
--   $$\{\omega\mid g(u,\xi(\omega))\le0\}=\{\omega\mid [S(u,\xi(\omega))](x)\le\alpha\ \ \forall x\in D\},$$
--   and this event is measurable.
--
--   This verifies Assumption 2.1(iv) for the PDE problem, so the general theory of §2.1 applies to (24), and it identifies the constraint (23d) with $\varphi(u)\ge p$.
--
--   **Formalization Note** The domain hypotheses are binders: `IsOpen D`, `Bornology.IsBounded D`, `D.Nonempty`, `d = 1 ∨ d = 2 ∨ d = 3`, `IsClassS D`, and `[CompactSpace (closure D)]` (a consequence of boundedness, needed for the norm on $C(\bar D)$). Nonemptiness of $D$ is added: the page's $\max_{x\in\bar D}$ needs it, and for $D=\emptyset$ Lean's supremum over the empty type is $0$. $A^{-1}$ is a continuous linear map `Ainv` together with the hypothesis `hA` that `Ainv F` is, on $\bar D$, a weak solution `IsDirichletSol D F y` for every $F\in L^2(D)$; Lemma 1.2 shows such a map exists and its uniqueness clause makes it the paper's $A^{-1}$. Lipschitz continuity is with respect to the product (max) norm on $L^2(D)\times\mathbb R^m$, equivalent to the sum norm used on the page.
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, p. 9, Lemma 2.9

import Mathlib
import Definitions.Def_ChanceStateCtrl_PDE_Setting
import Definitions.Def_ChanceStateCtrl_PDE_Model

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal Pointwise

namespace ChanceStateCtrl.PDE

/-- Lemma 2.9 (p. 9): `g(u, z) = max_{x ∈ D̄} [S(u, z)](x) - α` is jointly convex and globally
Lipschitzian on `L²(D) × ℝ^m`; the events `{g(u, ξ) ≤ 0}` and `{y(x, ω) ≤ α ∀ x ∈ D}` of (23d)
coincide and are measurable. -/
theorem lemma_2_9 {d m : ℕ} (D : Set (EuclideanSpace ℝ (Fin d)))
    (hDopen : IsOpen D) (hDbdd : Bornology.IsBounded D) (hDne : D.Nonempty)
    (hd : d = 1 ∨ d = 2 ∨ d = 3) (hDS : IsClassS D)
    [CompactSpace (closure D)] (Ainv : L2 D →L[ℝ] C(closure D, ℝ))
    (hA : ∀ F : L2 D, ∃ y, IsDirichletSol D (⇑F) y ∧ ∀ x : closure D, Ainv F x = y x)
    (f₀ : L2 D) (φ : Fin m → L2 D) (α : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (ξ : Ω → EuclideanSpace ℝ (Fin m)) (hξ : Measurable ξ) :
    ConvexOn ℝ Set.univ (Function.uncurry (gPDE Ainv f₀ φ α)) ∧
    (∃ C, LipschitzWith C (Function.uncurry (gPDE Ainv f₀ φ α))) ∧
    ∀ u : L2 D, MeasurableSet {w | gPDE Ainv f₀ φ α u (ξ w) ≤ 0} ∧
      {w | gPDE Ainv f₀ φ α u (ξ w) ≤ 0} =
        {w | ∀ x : closure D, x.1 ∈ D → stateS Ainv f₀ φ u (ξ w) x ≤ α} := by sorry

end ChanceStateCtrl.PDE
