-- Prove2me | Theorems.Thm_ChanceStateCtrl_PDE_lemma_1_2
-- name    : ChanceStateCtrl.PDE.lemma_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:21:40.623984+00:00
-- url     : https://prove2.me/theorems/4d17e48c-0274-40c7-b05f-a34aa3d6c00d
-- title:
--   Lemma 1.2, p. 3 — unique H¹₀(D) ∩ C(D̄) solution of the Dirichlet problem (2) and the bound (4)
-- statement:
--   Let $D\subseteq\mathbb R^d$ ($d\in\{1,2,3\}$) be a nonempty, open, bounded set of class S, and let $\varphi_1,\dots,\varphi_m\in L^2(D)$. Then:
--
--   1. for every $F\in L^2(D)$ the problem $-\Delta y=F$ in $D$, $y=0$ on $\partial D$, has a weak solution $y\in H^1_0(D)\cap C(\bar D)$;
--   2. two such solutions agree on $\bar D$;
--   3. there is a constant $C>0$ such that for all $u,f_0\in L^2(D)$ and $z\in\mathbb R^m$ the solution $\hat y(\cdot,z)$ of (2) with right-hand side $u+f_0+\sum_iz_i\varphi_i$ satisfies
--   $$\|\hat y(\cdot,z)\|_{C(\bar D)}\le C\big(\|z\|_2+\|u+f_0\|_{L^2(D)}\big).\tag{4}$$
--
--   This is the well-posedness result behind the solution operator $A^{-1}:L^2(D)\to C(\bar D)$ and the continuity of the control-to-state map $S$ used throughout the paper.
--
--   **Formalization Note** Taking $\Xi=\mathbb R^m$ as in §2. The constant $C$ is chosen after $D$ and $\varphi$ and before $u,f_0,z$; the paper applies (4) with $f_0=0$ as (7), which needs this uniformity. Uniqueness is stated on $\bar D$ because a function on $\mathbb R^d$ is only determined there. Nonemptiness of $D$ is a standing convention of the mission. The paper cites [26] for $d=2,3$.
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, p. 3, Lemma 1.2 (citing [26] for d = 2, 3), with Assumption 1.1

import Mathlib
import Definitions.Def_HunterPDE_Shared_WeakDeriv
import Definitions.Def_ChanceStateCtrl_PDE_Model

open MeasureTheory

namespace ChanceStateCtrl.PDE

/-- Lemma 1.2 (p. 3), with `Ξ = ℝ^m`: under Assumption 1.1 the Dirichlet problem (2) has, for
every right-hand side in `L²(D)`, a solution in `H¹₀(D) ∩ C(D̄)`, unique on `D̄`, and the
estimate (4) holds with a constant `C > 0` depending only on `D` and `φ`. -/
theorem lemma_1_2 {d m : ℕ} (D : Set (EuclideanSpace ℝ (Fin d)))
    (hDopen : IsOpen D) (hDbdd : Bornology.IsBounded D) (hDne : D.Nonempty)
    (hd : d = 1 ∨ d = 2 ∨ d = 3) (hDS : IsClassS D)
    (φ : Fin m → L2 D) :
    (∀ F : L2 D, ∃ y, IsDirichletSol D (⇑F) y) ∧
    (∀ (F : L2 D) (y₁ y₂ : EuclideanSpace ℝ (Fin d) → ℝ),
      IsDirichletSol D (⇑F) y₁ → IsDirichletSol D (⇑F) y₂ → Set.EqOn y₁ y₂ (closure D)) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ (f₀ u : L2 D) (z : EuclideanSpace ℝ (Fin m))
      (y : EuclideanSpace ℝ (Fin d) → ℝ),
      IsDirichletSol D (⇑(u + f₀ + ∑ i, z i • φ i)) y →
        ∀ x ∈ closure D, |y x| ≤ C * (‖z‖ + ‖u + f₀‖) := by sorry

end ChanceStateCtrl.PDE
