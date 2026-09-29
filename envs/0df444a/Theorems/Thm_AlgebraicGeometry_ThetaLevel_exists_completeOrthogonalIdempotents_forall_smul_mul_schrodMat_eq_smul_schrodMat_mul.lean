-- Prove2me | Theorems.Thm_AlgebraicGeometry_ThetaLevel_exists_completeOrthogonalIdempotents_forall_smul_mul_schrodMat_eq_smul_schrodMat_mul
-- name    : AlgebraicGeometry.ThetaLevel.exists_completeOrthogonalIdempotents_forall_smul_mul_schrodMat_eq_smul_schrodMat_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/0025a64c-99db-5fe3-a6e3-78621c38992f
-- title:
--   Idempotent splitting making T conjugate Schrödinger matrices into Schrödinger matrices
-- statement:
--   Fix $g$ and a tuple $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ of nonzero entries, put $H(\delta) = \prod_i \mathbb{Z}/\delta_i$, and let $N$ satisfy $\prod_i \delta_i = N+1$, with a bijection $e : \mathrm{Fin}(N+1) \simeq H(\delta)$. Let $B$ be a commutative ring in which $N+1$ is a unit, let $\zeta \in B$ satisfy $\zeta^{N+1} = 1$ and $1 - \zeta^j \in B^\times$ for all $0 < j < N+1$, and let $\omega \in B$ satisfy $\omega^2 = \zeta$. Let $S$ be a commutative ring, $\varphi_B : B \to S$ a ring homomorphism, and write $\vartheta(z)$ for `schrodMat δ (N+1) S (φB ω) e z`, the $(N+1)\times(N+1)$ matrix over $S$ whose $(i,j)$ entry is $(\varphi_B\omega)^{v}$, with $v$ the natural-number representative of $z.a + \sum_i \iota_i(z.k_i\,(e\,j)_i) \in \mathbb{Z}/2(N+1)$, when $e\,i = e\,j + z.h$, and $0$ otherwise; here $z = (a,h,k)$ ranges over `Heis δ (N+1)`, with $a \in \mathbb{Z}/2(N+1)$ and $h,k \in H(\delta)$. Assume $T$ is an invertible matrix over $S$ such that for every $z$ there are complete orthogonal idempotents $(\varepsilon_c)_{c \in H(\delta)\times H(\delta)}$ in $S$ and a unit $u \in S^\times$ with $T\,\vartheta(z) = \bigl(\sum_c \varepsilon_c\,(u\,\vartheta(0,c_1,c_2))\bigr)T$. Then there exist $m$, complete orthogonal idempotents $\varepsilon_1,\dots,\varepsilon_m$ of $S$, and maps $w_p : \mathrm{Heis}_\delta \to \mathrm{Heis}_\delta$ such that $\varepsilon_p\,(T\vartheta(z)) = \varepsilon_p\,(\vartheta(w_p z)\,T)$ for all $p$ and all $z$.
--
--   The statement is a normalisation step for the Schrödinger (Heisenberg) representation attached to a multiplicity tuple $\delta$: a matrix conjugating each $\vartheta(z)$ into a piecewise unit multiple of a monomial matrix is shown, after refining finitely many idempotent partitions of $\mathrm{Spec}\,S$ into one, to conjugate $\vartheta$ into $\vartheta$ of a relabelled Heisenberg element on each piece. It feeds [`AlgebraicGeometry.ThetaLevel.exists_idempotents_gam_units_mul_eq_mul_inter_of_forall_mul_schrodMat_eq`](thm.html#AlgebraicGeometry.ThetaLevel.exists_idempotents_gam_units_mul_eq_mul_inter_of_forall_mul_schrodMat_eq), where the relabelling maps are identified with automorphisms of the Heisenberg group; the multiplicativity of $z \mapsto \vartheta(z)$ comes from [`AlgebraicGeometry.ThetaLevel.schrodMat_one_and_schrodMat_mul`](thm.html#AlgebraicGeometry.ThetaLevel.schrodMat_one_and_schrodMat_mul), and the local diagonalisation of the occurring units from [`exists_completeOrthogonalIdempotents_mul_eq_pow_mul_of_pow_eq_one_of_forall_isUnit_one_sub_pow`](thm.html#exists_completeOrthogonalIdempotents_mul_eq_pow_mul_of_pow_eq_one_of_forall_isUnit_one_sub_pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ThetaLevel_exists_completeOrthogonalIdempotents_forall_smul_mul_schrodMat_eq_smul_schrodMat_mul.lean

import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped BigOperators
open AlgebraicGeometry AlgebraicGeometry.ThetaLevel

theorem AlgebraicGeometry.ThetaLevel.exists_completeOrthogonalIdempotents_forall_smul_mul_schrodMat_eq_smul_schrodMat_mul
    {g : ℕ} (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)] (N : ℕ) (hδd : ∏ i, δ i = N + 1)
    (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i)))
    (B : Type) [CommRing B] (hd : IsUnit ((N + 1 : ℕ) : B))
    (ζ : B) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    (ω : B) (hω : ω ^ 2 = ζ)
    {S : Type} [CommRing S] (φB : B →+* S)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) S) (hT : IsUnit T)
    (hmono : ∀ z : Heis δ (N + 1), ∃ (ε : ((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i)) → S) (u : Sˣ),
      CompleteOrthogonalIdempotents ε ∧
        T * schrodMat δ (N + 1) S (φB ω) e z =
          (∑ c, ε c • ((u : S) • schrodMat δ (N + 1) S (φB ω) e ⟨0, c.1, c.2⟩)) * T) :
    ∃ (m : ℕ) (ε : Fin m → S) (w : Fin m → Heis δ (N + 1) → Heis δ (N + 1)),
      CompleteOrthogonalIdempotents ε ∧
      ∀ (p : Fin m) (z : Heis δ (N + 1)),
        ε p • (T * schrodMat δ (N + 1) S (φB ω) e z) = ε p • (schrodMat δ (N + 1) S (φB ω) e (w p z) * T) := by sorry
