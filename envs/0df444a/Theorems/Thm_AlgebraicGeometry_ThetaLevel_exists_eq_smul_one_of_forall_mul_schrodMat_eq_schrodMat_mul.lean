-- Prove2me | Theorems.Thm_AlgebraicGeometry_ThetaLevel_exists_eq_smul_one_of_forall_mul_schrodMat_eq_schrodMat_mul
-- name    : AlgebraicGeometry.ThetaLevel.exists_eq_smul_one_of_forall_mul_schrodMat_eq_schrodMat_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/8283af60-69e4-5042-b740-7c195ae1765f
-- title:
--   Schur's lemma for the Schrödinger matrices of Heis_δ
-- statement:
--   Fix $g \in \mathbb{N}$ and a tuple $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ with every $\delta_i$ nonzero, and a nonzero $d \in \mathbb{N}$ with $\prod_i \delta_i = d$. Let $B$ be a commutative ring and $\zeta, \omega \in B$ with $\zeta^d = 1$, with $1 - \zeta^j$ a unit of $B$ for every natural $j$ with $0 < j < d$, and with $\omega^2 = \zeta$. Let $n \in \mathbb{N}$ and let $e : \mathrm{Fin}\,n \simeq \mathrm{HH}\,\delta$ be a bijection onto $\mathrm{HH}\,\delta = \prod_i \mathbb{Z}/\delta_i$. For $z$ in the finite Heisenberg index set `Heis δ d`, whose elements consist of $z.a \in \mathbb{Z}/2d$ and $z.h, z.k \in \mathrm{HH}\,\delta$, the Schrödinger matrix `schrodMat δ d B ω e z` has $(i,j)$ entry $\omega^{v}$, with $v$ the natural representative of $z.a + \mathrm{pair}(z.k, e_j) \in \mathbb{Z}/2d$, when $e_i = e_j + z.h$, and entry $0$ otherwise; here $\mathrm{pair}(k,h) = \sum_i \mathtt{iota}\,\delta\,d\,i\,(k_i h_i)$ for the coordinate maps `iota δ d i` into $\mathbb{Z}/2d$. The assertion is: if $T$ is an $n \times n$ matrix over $B$ such that $T \cdot \mathtt{schrodMat}\,\delta\,d\,B\,\omega\,e\,z = \mathtt{schrodMat}\,\delta\,d\,B\,\omega\,e\,z \cdot T$ for every $z$, then there is $c \in B$ with $T = c \cdot 1$.
--
--   This is Schur's lemma for the Schrödinger representation of the finite Heisenberg group attached to the type $\delta$, in the form used by Mumford in the theory of theta structures: the commutant of the Schrödinger matrices over a ring carrying a suitably nondegenerate $d$-th root of unity consists of the scalars. It feeds the rigidity statements for theta level structures, in particular the comparison and reframing results for framed polarised abelian schemes and the construction of complete orthogonal idempotents diagonalising the Schrödinger matrices.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ThetaLevel_exists_eq_smul_one_of_forall_mul_schrodMat_eq_schrodMat_mul.lean

import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped BigOperators
open AlgebraicGeometry AlgebraicGeometry.ThetaLevel

theorem AlgebraicGeometry.ThetaLevel.exists_eq_smul_one_of_forall_mul_schrodMat_eq_schrodMat_mul
    {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (d : ℕ) [NeZero d] (hδd : ∏ i, δ i = d)
    (B : Type) [CommRing B] (ζ ω : B) (hζ : ζ ^ d = 1) (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - ζ ^ j))
    (hω : ω ^ 2 = ζ) {n : ℕ} (e : Fin n ≃ HH δ)
    (T : Matrix (Fin n) (Fin n) B) (hT : ∀ z : Heis δ d, T * schrodMat δ d B ω e z = schrodMat δ d B ω e z * T) :
    ∃ c : B, T = c • (1 : Matrix (Fin n) (Fin n) B) := by sorry
