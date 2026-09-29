-- Prove2me | Theorems.Thm_AlgebraicGeometry_ThetaLevel_exists_completeOrthogonalIdempotents_smul_eq_smul_schrodMat_of_forall_mul_schrodMat_eq_smul
-- name    : AlgebraicGeometry.ThetaLevel.exists_completeOrthogonalIdempotents_smul_eq_smul_schrodMat_of_forall_mul_schrodMat_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/f5cfa58a-f997-5d8d-b79a-17062f8651a2
-- title:
--   Piecewise normal form for matrices normalising the Schrödinger matrices
-- statement:
--   Fix $g$ and $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ with all $\delta_i$ nonzero, and $d \neq 0$ with $\prod_i \delta_i = d$; write $H = H(\delta) = \prod_i \mathbb{Z}/\delta_i$. Let $B$ be a commutative ring in which the image of $d$ is a unit, and let $\zeta, \omega \in B$ satisfy $\zeta^d = 1$, $1 - \zeta^j \in B^{\times}$ for all integers $0 < j < d$, and $\omega^2 = \zeta$. Fix a bijection $e : \mathrm{Fin}\,n \simeq H$, and for $z = (a, h, k)$ in the Heisenberg set $\mathrm{Heis}(\delta,d) = \mathbb{Z}/2d \times H \times H$ let $\vartheta(z) \in M_n(B)$ be the matrix with $(i,j)$ entry $\omega^{\,(a + \mathrm{pair}(k, e\,j)).\mathrm{val}}$ when $e\,i = e\,j + h$ and $0$ otherwise, where $\mathrm{pair}(k,h) = \sum_i \iota_i(k_i h_i) \in \mathbb{Z}/2d$. Let $T \in M_n(B)$ be a unit, and suppose given $\lambda, \mu : H \to B$ with $T\,\vartheta(0,h',0) = \lambda(h') \cdot \bigl(\vartheta(0,h',0)\,T\bigr)$ and $T\,\vartheta(0,0,k') = \mu(k') \cdot \bigl(\vartheta(0,0,k')\,T\bigr)$ for all $h', k' \in H$. Then there exist a family $\varepsilon : H \times H \to B$ of complete orthogonal idempotents and a unit $u \in B^{\times}$ such that $\varepsilon_{(h,k)} \cdot T = (\varepsilon_{(h,k)} u) \cdot \vartheta(0,h,k)$ for every $(h,k) \in H \times H$.
--
--   This is the linear-algebra core of the theta-group normal form: a matrix conjugating the Schrödinger representation of the finite Heisenberg group into itself up to scalars on each of the two Lagrangian families is, after decomposing $\operatorname{Spec} B$ into the clopen pieces cut out by a complete family of orthogonal idempotents indexed by $H \times H$, a unit multiple of a single monomial Schrödinger matrix $\vartheta(0,h,k)$. It is used to produce the corresponding idempotent decomposition for Schrödinger frames of framed polarised abelian schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ThetaLevel_exists_completeOrthogonalIdempotents_smul_eq_smul_schrodMat_of_forall_mul_schrodMat_eq_smul.lean

import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped BigOperators
open AlgebraicGeometry AlgebraicGeometry.ThetaLevel

theorem AlgebraicGeometry.ThetaLevel.exists_completeOrthogonalIdempotents_smul_eq_smul_schrodMat_of_forall_mul_schrodMat_eq_smul
    {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (d : ℕ) [NeZero d] (hδd : ∏ i, δ i = d)
    (B : Type) [CommRing B] (hd : IsUnit ((d : ℕ) : B)) (ζ ω : B) (hζ : ζ ^ d = 1)
    (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - ζ ^ j)) (hω : ω ^ 2 = ζ) {n : ℕ} (e : Fin n ≃ HH δ)
    (T : Matrix (Fin n) (Fin n) B) (hT : IsUnit T) (lam mu : HH δ → B)
    (hθ : ∀ h' : HH δ, T * schrodMat δ d B ω e (Heis.theta h') = lam h' • (schrodMat δ d B ω e (Heis.theta h') * T))
    (hη : ∀ k' : HH δ, T * schrodMat δ d B ω e (Heis.eta k') = mu k' • (schrodMat δ d B ω e (Heis.eta k') * T)) :
    ∃ (ε : HH δ × HH δ → B) (u : Bˣ), CompleteOrthogonalIdempotents ε ∧
      ∀ c : HH δ × HH δ, ε c • T = (ε c * u) • schrodMat δ d B ω e ⟨0, c.1, c.2⟩ := by sorry
