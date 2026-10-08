-- Prove2me | Theorems.Thm_DiffVI_Cone_lemma_8_1
-- name    : DiffVI.Cone.lemma_8_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:39.850971+00:00
-- url     : https://prove2.me/theorems/baedd44b-d1d1-4ac1-bf20-314d97e458e1
-- title:
--   Lemma 8.1, p. 56 — condition (E) is equivalent to the coordinate exchange property (8.6)
-- statement:
--   Let $E\in\mathbb R^{\ell\times m}$ and let $Z\in\mathbb R^{m\times k}$, $W\in\mathbb R^{m\times p}$ have orthonormal columns forming bases of $\ker E$ and $(\ker E)^\perp$, so that $P=[Z\ W]$ is orthogonal. For any set $K\subseteq\mathbb R^m$, condition (E), $K_1\oplus K_2\subseteq K$ where $K_1$, $K_2$ are the orthogonal projections of $K$ onto $\ker E$ and $(\ker E)^\perp$, holds if and only if
--   $$\Big[\,Z\mu^i+W\lambda^i\in K,\ i=1,2\,\Big]\ \Longrightarrow\ Z\mu^1+W\lambda^2\in K.\tag{8.6}$$
--
--   In the paper's notation $Z\mu+W\lambda\in K$ is $(\mu,\lambda)\in P^\top K$. The lemma lets one swap the $\mathcal E^\perp$-component of one point of $K$ into another, which is how the bounds of Lemma 8.2 and Proposition 8.3 test the variational inequality.
--
--   **Formalization Note** (E) is defined basis-free with Mathlib's orthogonal projections, so the equivalence has content.
-- source:
--   Pang & Stewart, Differential variational inequalities, author's version hal-01366027v1, p. 56, Lemma 8.1, (8.6)

import Mathlib
import Definitions.Def_SolodovSvaiterVI_Alg21_viSol
import Definitions.Def_DiffVI_Cone_Setting

open scoped InnerProductSpace InnerProduct
open SolodovSvaiterVI.Alg21

namespace DiffVI.Cone

theorem lemma_8_1 {m ℓ k p : ℕ} (K : Set (EuclideanSpace ℝ (Fin m)))
    (E : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin ℓ))
    (Z : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)) (W : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hZW : IsZWBasis E Z W) :
    CondE K E ↔
      ∀ μ1 μ2 : EuclideanSpace ℝ (Fin k), ∀ lam1 lam2 : EuclideanSpace ℝ (Fin p),
        Z μ1 + W lam1 ∈ K → Z μ2 + W lam2 ∈ K → Z μ1 + W lam2 ∈ K := by sorry

end DiffVI.Cone
