-- Prove2me | Theorems.Thm_DeepONetError_optimal_projection
-- name    : DeepONetError.optimal_projection
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T05:25:25.519355+00:00
-- url     : https://prove2.me/theorems/67a6e91b-4073-4a5a-b1f6-95608311e173
-- title:
--   Lemma 3.13: the optimal projector of an affine reconstructor
-- statement:
--   Let $U\subset\mathbb{R}^n$. Let $\mathcal{R}(\alpha)=\tau_0+\sum_{k=1}^p\alpha_k\tau_k$ with $\tau_0\in L^2(U)$ and linearly independent $\tau_1,\dots,\tau_p\in L^2(U)$, and let $\nu\in\mathcal{P}_2(L^2(U))$. Let $\tau^*_1,\dots,\tau^*_p\in\mathrm{span}(\tau_1,\dots,\tau_p)$ be the dual basis, $\langle\tau_\ell,\tau^*_k\rangle=\delta_{\ell k}$. Then:
--   1. The reconstruction error $\widehat{\mathcal{E}}_{\mathcal{R}}$ is minimized over all Borel measurable projectors $\mathcal{P}:L^2(U)\to\mathbb{R}^p$ by
--   $$\mathcal{P}(u)=\big(\langle u-\tau_0,\tau^*_1\rangle,\dots,\langle u-\tau_0,\tau^*_p\rangle\big).$$
--   2. For this $\mathcal{P}$,
--   $$\mathcal{R}\circ\mathcal{P}(u)=\tau_0^\perp+\sum_{k=1}^p\langle u,\tau^*_k\rangle\tau_k,\qquad\tau_0^\perp=\tau_0-\sum_{k=1}^p\langle\tau_0,\tau^*_k\rangle\tau_k,$$
--   and $\tau_0^\perp$ is the orthogonal projection of $\tau_0$ onto $\mathrm{span}(\tau_1,\dots,\tau_p)^\perp$.
--
--   **Formalization Note** The dual basis is defined explicitly through the inverse Gram matrix, $\tau^*_k=\sum_j(\mathrm{Gram}^{-1})_{kj}\tau_j$. Its two defining properties (it lies in the span and is dual to $\tau_1,\dots,\tau_p$) are included as conclusions. That $\tau_0^\perp$ is the orthogonal projection onto the complement is stated as: $\tau_0^\perp$ lies in the complement and $\tau_0-\tau_0^\perp$ lies in the span.
-- source:
--   Lanthaler, Mishra and Karniadakis, Error estimates for DeepOnets: A deep learning framework in infinite dimensions, arXiv:2102.09618v3 (2022), Section 3.4, Lemma 3.13, eqs. (3.19)-(3.20), p. 19; proof in Appendix C.4, p. 85

import Mathlib
import Definitions.Def_DeepONetError_Basic

open MeasureTheory

namespace DeepONetError

theorem optimal_projection {n p : ℕ} {U : Set (Fin n → ℝ)}
    [MeasurableSpace (L2 U)] [BorelSpace (L2 U)]
    (tau : Fin (p + 1) → L2 U) (htau : LinearIndependent ℝ (fun k : Fin p => tau k.succ))
    (nu : Measure (L2 U)) (hnu : IsP2 nu) :
    (∀ k, dualBasis (fun j => tau j.succ) k ∈
      Submodule.span ℝ (Set.range fun j : Fin p => tau j.succ)) ∧
    (∀ k l : Fin p, inner ℝ (tau l.succ) (dualBasis (fun j => tau j.succ) k) =
      if l = k then 1 else 0) ∧
    (∀ Proj : L2 U → EuclideanSpace ℝ (Fin p), Measurable Proj →
      recErr nu (trunkRec tau) (optProj tau) ≤ recErr nu (trunkRec tau) Proj) ∧
    (∀ u : L2 U, trunkRec tau (optProj tau u) =
      (tau 0 - ∑ k, inner ℝ (tau 0) (dualBasis (fun j => tau j.succ) k) • tau k.succ) +
        ∑ k, inner ℝ u (dualBasis (fun j => tau j.succ) k) • tau k.succ) ∧
    (tau 0 - ∑ k, inner ℝ (tau 0) (dualBasis (fun j => tau j.succ) k) • tau k.succ ∈
        (Submodule.span ℝ (Set.range fun j : Fin p => tau j.succ))ᗮ ∧
      ∑ k, inner ℝ (tau 0) (dualBasis (fun j => tau j.succ) k) • tau k.succ ∈
        Submodule.span ℝ (Set.range fun j : Fin p => tau j.succ)) := by sorry

end DeepONetError
