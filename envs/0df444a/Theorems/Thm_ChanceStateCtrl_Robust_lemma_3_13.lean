-- Prove2me | Theorems.Thm_ChanceStateCtrl_Robust_lemma_3_13
-- name    : ChanceStateCtrl.Robust.lemma_3_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:16:40.51737+00:00
-- url     : https://prove2.me/theorems/d9831654-2f65-4ca0-8488-df3d39ad433f
-- title:
--   Lemma 3.13, p. 23 — unique solution ŷ ∈ C(D̄ × Ξ) of (63b)–(63c) and the bound (64)
-- statement:
--   Let $D\subseteq\mathbb R^d$ ($d\in\{1,2,3\}$) be open, bounded and of class S, let $\Xi\subset\mathbb R^m$ be compact, and let $\varphi_1,\dots,\varphi_m\in L^2(D)$ (Assumption 1.1). Then:
--
--   1. for all $f_0,u\in L^2(D)$ there is exactly one $\hat y\in C(\bar D\times\Xi)$ solving the parametrized problem
--   $$-\Delta\hat y(x,z)=u(x)+f(x,z)\ \ (x,z)\in D\times\Xi,\qquad \hat y(x,z)=0\ \ (x,z)\in\partial D\times\Xi,$$
--   where $f(\cdot,z)=f_0+\sum_i z_i\varphi_i$ and each slice $\hat y(\cdot,z)$ is the weak solution in $H^1_0(D)\cap C(\bar D)$;
--   2. there is a constant $C>0$ such that every such solution satisfies
--   $$\|\hat y\|_{C(\bar D\times\Xi)}\le C\Big(\max_{z\in\Xi}\|z\|_2+\|u+f_0\|_{L^2(D)}\Big).\tag{64}$$
--
--   This well-posedness result is what allows the robust control-to-state operator $\hat{\mathcal S}:L^2(D)\to C(\bar D\times\Xi)$ to be defined.
--
--   **Formalization Note** The constant $C$ is uniform in $u$ and in $f_0$ (it may depend on $D$, $\Xi$ and the $\varphi_i$), as in Lemma 1.2's estimate (4). The maximum over $\Xi$ is written as a supremum, which is the maximum for nonempty compact $\Xi$ and $0$ for empty $\Xi$ (then $C(\bar D\times\Xi)=\{0\}$ and the bound is trivial).
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, p. 23, Lemma 3.13, (64)

import Mathlib
import Definitions.Def_ChanceStateCtrl_Robust_Setting

open MeasureTheory

namespace ChanceStateCtrl.Robust

theorem lemma_3_13 {d m : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))} {Ξ : Set (EuclideanSpace ℝ (Fin m))}
    (hDopen : IsOpen D) (hDbdd : Bornology.IsBounded D) (hd : d = 1 ∨ d = 2 ∨ d = 3)
    (hS : ChanceStateCtrl.PDE.IsClassS D) [CompactSpace (closure D)] [CompactSpace Ξ]
    (phi : Fin m → ChanceStateCtrl.PDE.L2 D) :
    (∀ f0 u : ChanceStateCtrl.PDE.L2 D, ∃! yhat : C(closure D × Ξ, ℝ), IsRobustStateSol f0 phi u yhat) ∧
      ∃ C > (0 : ℝ), ∀ (f0 u : ChanceStateCtrl.PDE.L2 D) (yhat : C(closure D × Ξ, ℝ)),
        IsRobustStateSol f0 phi u yhat →
          ‖yhat‖ ≤ C * (sSup ((fun z => ‖z‖) '' Ξ) + ‖u + f0‖) := by sorry

end ChanceStateCtrl.Robust
