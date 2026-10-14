-- Prove2me | Theorems.Thm_ChanceStateCtrl_PDE_lemma_2_10
-- name    : ChanceStateCtrl.PDE.lemma_2_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:21:41.805594+00:00
-- url     : https://prove2.me/theorems/cbb947b4-411e-45b8-bf12-50a4b652efb7
-- title:
--   Lemma 2.10, p. 10 — g of (24) satisfies the moderate growth condition (12) at every ū ∈ L²(D)
-- statement:
--   Throughout, $D\subseteq\mathbb R^d$ ($d\in\{1,2,3\}$) is a nonempty, open, bounded domain of class S, $A^{-1}:L^2(D)\to C(\bar D)$ is the solution operator of the Dirichlet problem $-\Delta y=F$ in $D$, $y=0$ on $\partial D$ (in $H^1_0(D)\cap C(\bar D)$), $f_0,\varphi_1,\dots,\varphi_m\in L^2(D)$, and $S(u,z)=A^{-1}(u+f_0+\sum_i z_i\varphi_i)$, $P(u,z)=A^{-1}u+\sum_i z_iA^{-1}\varphi_i$ are the operators of (5). The constraint function of (24) is $g(u,z)=\max_{x\in\bar D}[S(u,z)](x)-\alpha$ for a threshold $\alpha\in\mathbb R$.
--
--   Let $\Sigma\in\mathbb R^{m\times m}$ ($m\ge1$) be positive definite. Then for every $\bar u\in L^2(D)$ the condition of moderate growth (12) holds: there is $l>0$ such that
--   $$g^\circ(\cdot,z)(u;h)\le l\,\|z\|_2^{-m}\exp\Big(\frac{\|z\|_2^2}{2\|\Sigma^{1/2}\|^2}\Big)\|h\|_{L^2(D)}$$
--   for all $h\in L^2(D)$, all $u$ with $\|u-\bar u\|<1/l$ and all $z$ with $\|z\|_2\ge l$.
--
--   This is the growth hypothesis of Theorem 2.2; it holds at every point for the PDE problem, even when the set $M$ of (11) is unbounded.
--
--   **Formalization Note** The domain hypotheses are binders: `IsOpen D`, `Bornology.IsBounded D`, `D.Nonempty`, `d = 1 ∨ d = 2 ∨ d = 3`, `IsClassS D`, and `[CompactSpace (closure D)]` (a consequence of boundedness, needed for the norm on $C(\bar D)$). Nonemptiness of $D$ is added: the page's $\max_{x\in\bar D}$ needs it, and for $D=\emptyset$ Lean's supremum over the empty type is $0$. $A^{-1}$ is a continuous linear map `Ainv` together with the hypothesis `hA` that `Ainv F` is, on $\bar D$, a weak solution `IsDirichletSol D F y` for every $F\in L^2(D)$; Lemma 1.2 shows such a map exists and its uniqueness clause makes it the paper's $A^{-1}$. The Clarke directional derivative is the page-3 limsup with denominator $t$ (the page prints $h$, a misprint), and the dual of $L^2(D)$ is identified with $L^2(D)$ through the inner product, as on p. 11. $\Sigma^{1/2}$ is the positive semidefinite square root `CFC.sqrt Sigma`, the root used by Mathlib's `multivariateGaussian`.
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, p. 10, Lemma 2.10

import Mathlib
import Definitions.Def_ChanceStateCtrl_PDE_Setting
import Definitions.Def_ChanceStateCtrl_PDE_Model

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal Pointwise

namespace ChanceStateCtrl.PDE

/-- Lemma 2.10 (p. 10): at every `ū ∈ L²(D)` the constraint function `g` of (24) satisfies the
condition of moderate growth (12). -/
theorem lemma_2_10 {d m : ℕ} (D : Set (EuclideanSpace ℝ (Fin d)))
    (hDopen : IsOpen D) (hDbdd : Bornology.IsBounded D) (hDne : D.Nonempty)
    (hd : d = 1 ∨ d = 2 ∨ d = 3) (hDS : IsClassS D)
    [CompactSpace (closure D)] (Ainv : L2 D →L[ℝ] C(closure D, ℝ))
    (hA : ∀ F : L2 D, ∃ y, IsDirichletSol D (⇑F) y ∧ ∀ x : closure D, Ainv F x = y x)
    (f₀ : L2 D) (φ : Fin m → L2 D) (α : ℝ)
    (hm : 0 < m) (Sigma : Matrix (Fin m) (Fin m) ℝ) (hSigma : Sigma.PosDef)
    (ubar : L2 D) :
    ModerateGrowth (gPDE Ainv f₀ φ α) Sigma ubar := by sorry

end ChanceStateCtrl.PDE
