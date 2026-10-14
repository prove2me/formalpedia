-- Prove2me | Theorems.Thm_ChanceStateCtrl_PDE_lemma_1_4
-- name    : ChanceStateCtrl.PDE.lemma_1_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:21:28.545091+00:00
-- url     : https://prove2.me/theorems/e9959a57-aa2f-4d9f-b75b-f83554400be9
-- title:
--   Lemma 1.4, p. 4 — for each x ∈ D̄ the random state ω ↦ y(x, ω) is measurable
-- statement:
--   Throughout, $D\subseteq\mathbb R^d$ ($d\in\{1,2,3\}$) is a nonempty, open, bounded domain of class S, $A^{-1}:L^2(D)\to C(\bar D)$ is the solution operator of the Dirichlet problem $-\Delta y=F$ in $D$, $y=0$ on $\partial D$ (in $H^1_0(D)\cap C(\bar D)$), $f_0,\varphi_1,\dots,\varphi_m\in L^2(D)$, and $S(u,z)=A^{-1}(u+f_0+\sum_i z_i\varphi_i)$, $P(u,z)=A^{-1}u+\sum_i z_iA^{-1}\varphi_i$ are the operators of (5). The constraint function of (24) is $g(u,z)=\max_{x\in\bar D}[S(u,z)](x)-\alpha$ for a threshold $\alpha\in\mathbb R$.
--
--   Let $\xi:\Omega\to\mathbb R^m$ be a measurable random vector on a measurable space $\Omega$. For every control $u\in L^2(D)$ and every $x\in\bar D$, the map
--   $$\omega\mapsto y(x,\omega)=[S(u,\xi(\omega))](x)$$
--   is measurable.
--
--   This justifies the random PDE (8): the state at each point is a random variable.
--
--   **Formalization Note** The domain hypotheses are binders: `IsOpen D`, `Bornology.IsBounded D`, `D.Nonempty`, `d = 1 ∨ d = 2 ∨ d = 3`, `IsClassS D`, and `[CompactSpace (closure D)]` (a consequence of boundedness, needed for the norm on $C(\bar D)$). Nonemptiness of $D$ is added: the page's $\max_{x\in\bar D}$ needs it, and for $D=\emptyset$ Lean's supremum over the empty type is $0$. $A^{-1}$ is a continuous linear map `Ainv` together with the hypothesis `hA` that `Ainv F` is, on $\bar D$, a weak solution `IsDirichletSol D F y` for every $F\in L^2(D)$; Lemma 1.2 shows such a map exists and its uniqueness clause makes it the paper's $A^{-1}$.
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, p. 4, Lemma 1.4

import Mathlib
import Definitions.Def_ChanceStateCtrl_PDE_Setting
import Definitions.Def_ChanceStateCtrl_PDE_Model

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal Pointwise

namespace ChanceStateCtrl.PDE

/-- Lemma 1.4 (p. 4): for each `x ∈ D̄` and each control `u`, the random state
`ω ↦ y(x, ω) = [S(u, ξ(ω))](x)` is measurable. -/
theorem lemma_1_4 {d m : ℕ} (D : Set (EuclideanSpace ℝ (Fin d)))
    (hDopen : IsOpen D) (hDbdd : Bornology.IsBounded D) (hDne : D.Nonempty)
    (hd : d = 1 ∨ d = 2 ∨ d = 3) (hDS : IsClassS D)
    [CompactSpace (closure D)] (Ainv : L2 D →L[ℝ] C(closure D, ℝ))
    (hA : ∀ F : L2 D, ∃ y, IsDirichletSol D (⇑F) y ∧ ∀ x : closure D, Ainv F x = y x)
    (f₀ : L2 D) (φ : Fin m → L2 D) (α : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (ξ : Ω → EuclideanSpace ℝ (Fin m)) (hξ : Measurable ξ)
    (u : L2 D) (x : closure D) :
    Measurable (fun w => stateS Ainv f₀ φ u (ξ w) x) := by sorry

end ChanceStateCtrl.PDE
