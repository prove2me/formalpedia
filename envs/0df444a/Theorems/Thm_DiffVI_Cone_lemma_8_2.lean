-- Prove2me | Theorems.Thm_DiffVI_Cone_lemma_8_2
-- name    : DiffVI.Cone.lemma_8_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:23.381994+00:00
-- url     : https://prove2.me/theorems/38067753-baf7-41ef-882f-baeb1c6f00a6
-- title:
--   Lemma 8.2, p. 57 — under (8.8), q ↦ E SOL(K, q + Φ_h + F) is single-valued and Lipschitz with a constant independent of h
-- statement:
--   Let $\emptyset\ne K\subseteq\mathbb R^m$ be closed and convex and satisfy (E). Let $F=E^\top\circ\Psi\circ E$ satisfy (C′), let $Z$, $W$ be orthonormal bases of $\ker E$ and $(\ker E)^\perp$, and let $\Upsilon=(EW)^\top\circ\Psi\circ(EW)$ satisfy (8.7) with $\eta_\Upsilon>0$. For all $\eta_\Phi,L_\Phi>0$ there is a constant $c>0$ such that for every $h>0$ with
--   $$0<h<\frac12\,\frac{\eta_\Upsilon}{L_\Phi\|W\|^2\big(1+L_\Phi/\eta_\Phi\big)}\tag{8.8}$$
--   and every $\Phi_h:\mathbb R^m\to\mathbb R^m$ that is strongly monotone on $\mathbb R^m$ with modulus $h\eta_\Phi$ and Lipschitz continuous with constant $hL_\Phi$:
--
--   1. $\mathrm{SOL}(K,q+\Phi_h+F)\ne\emptyset$ for every $q\in\mathbb R^m$;
--   2. for all $q^1,q^2$ and all $u^i\in\mathrm{SOL}(K,q^i+\Phi_h+F)$,
--   $$\|Eu^1-Eu^2\|\le c\,\|q^1-q^2\|.$$
--
--   So $q\mapsto E\,\mathrm{SOL}(K,q+\Phi_h+F)$ is single-valued and Lipschitz continuous, with a constant independent of $h$. In the proof of Theorem 8.1 this gives the bound (7.6) on $\|Eu^{h,i+1}-Eu^{h,i}\|$.
--
--   **Formalization Note** (8.8) is multiplied out, $2h\,L_\Phi\|W\|^2(1+L_\Phi/\eta_\Phi)<\eta_\Upsilon$, so that $W=0$ (the case $E=0$) imposes no restriction. "Single-valued" is read as nonempty (part 1) plus at most one value (part 2 with $q^1=q^2$). The page does not list hypotheses on $K$; the standing assumptions of §8 that the proof uses are added: $K$ nonempty, closed and convex (for existence) and (E) (through Lemma 8.1). The order "there is $c$, for all $h$" expresses independence of $h$.
-- source:
--   Pang & Stewart, Differential variational inequalities, author's version hal-01366027v1, p. 57, Lemma 8.2, (8.8)

import Mathlib
import Definitions.Def_SolodovSvaiterVI_Alg21_viSol
import Definitions.Def_DiffVI_Cone_Setting

open scoped InnerProductSpace InnerProduct
open SolodovSvaiterVI.Alg21

namespace DiffVI.Cone

theorem lemma_8_2 {m ℓ k p : ℕ} (K : Set (EuclideanSpace ℝ (Fin m))) (hKne : K.Nonempty)
    (hKcl : IsClosed K) (hKcv : Convex ℝ K)
    (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (E : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin ℓ)) (Ψ : EuclideanSpace ℝ (Fin ℓ) → EuclideanSpace ℝ (Fin ℓ))
    (hC' : CondC' F E Ψ) (hE : CondE K E)
    (Z : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)) (W : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hZW : IsZWBasis E Z W) (ηΥ : ℝ) (hΥ : CondUps E W Ψ ηΥ) :
    ∀ ηΦ LΦ : ℝ, 0 < ηΦ → 0 < LΦ → ∃ c : ℝ, 0 < c ∧
      ∀ h : ℝ, 0 < h → 2 * h * (LΦ * ‖W‖ ^ 2 * (1 + LΦ / ηΦ)) < ηΥ →
        ∀ Φh : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m),
          DiffVI.Exist.IsStronglyMonotoneOn Φh Set.univ (h * ηΦ) →
          (∀ v v' : EuclideanSpace ℝ (Fin m), ‖Φh v - Φh v'‖ ≤ h * LΦ * ‖v - v'‖) →
          (∀ q : EuclideanSpace ℝ (Fin m), (viSol (fun v => q + Φh v + F v) K).Nonempty) ∧
          ∀ q1 q2 : EuclideanSpace ℝ (Fin m), ∀ u1 ∈ viSol (fun v => q1 + Φh v + F v) K,
            ∀ u2 ∈ viSol (fun v => q2 + Φh v + F v) K, ‖E u1 - E u2‖ ≤ c * ‖q1 - q2‖ := by sorry

end DiffVI.Cone
