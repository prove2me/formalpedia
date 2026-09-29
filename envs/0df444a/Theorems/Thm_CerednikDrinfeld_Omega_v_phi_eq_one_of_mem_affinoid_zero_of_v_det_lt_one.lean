-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_v_phi_eq_one_of_mem_affinoid_zero_of_v_det_lt_one
-- name    : CerednikDrinfeld.Omega.v_phi_eq_one_of_mem_affinoid_zero_of_v_det_lt_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/d2810101-0f7f-5e56-a1c1-0b7fa98a76e1
-- title:
--   Valuation exactly one on the level-0 affinoid under non-unit determinant
-- statement:
--   Let $K_0$ be a field and $K$ a field which is a $K_0$-algebra, and let $K$ carry a valuation $v =$ `Valued.v` with values in a linearly ordered commutative group with zero $\Gamma_0$. Let $\varpi_1$ be a pseudo-uniformiser of the pair, that is an element $\varpi_1 \in K_0$ with $0 < v(\varpi_1) < 1$ in $K$ and such that every nonzero $a \in K_0$ satisfies $v(\varpi_1)^N \le v(a) \le v(\varpi_1)^{-N}$ for some $N \in \mathbb{N}$. Let $w, u \in K$ both lie in the level-$0$ affinoid of $\varpi_1$, i.e. $v(w) \le 1$ and $v(w - a) \ge 1$ for every $a \in K_0$ with $v(a) \le 1$, and likewise for $u$. Let $m$ be a $2 \times 2$ matrix over $K_0$ whose entries all satisfy $v(m_{ij}) \le 1$, with $v(m_{ij}) = 1$ for at least one pair $(i,j)$, and with $v(\det m) < 1$. Then
--   $$v\bigl(w\,(m_{10}u + m_{11}) - (m_{00}u + m_{01})\bigr) = 1,$$
--   all entries being read in $K$ via the structure map.
--
--   This is the level-$0$ instance of the two-point pairing estimate on the Drinfeld upper half plane: a matrix over $K_0$ with unit-normalised entries but non-unit determinant moves the standard vertex of the Bruhat–Tits tree, and the displayed expression — the numerator of the difference $w - m\cdot u$ of Möbius coordinates — then has valuation exactly $1$. It feeds the computation of the standard vertex under the $\mathrm{PGL}_2$ action on the level-$0$ affinoid and the identification of the valuation of a cross ratio of Möbius images with a power of $q$ indexed by the overlap of two walks in the tree.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_v_phi_eq_one_of_mem_affinoid_zero_of_v_det_lt_one.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.v_phi_eq_one_of_mem_affinoid_zero_of_v_det_lt_one
    {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ₁ : PseudoUniformizer K₀ K) {w u : K} (hw : w ∈ affinoid ϖ₁ 0) (hu : u ∈ affinoid ϖ₁ 0)
    (m : Matrix (Fin 2) (Fin 2) K₀)
    (hle : ∀ i j : Fin 2, Valued.v (algebraMap K₀ K (m i j)) ≤ 1)
    (hone : ∃ i j : Fin 2, Valued.v (algebraMap K₀ K (m i j)) = 1)
    (hdet : Valued.v (algebraMap K₀ K m.det) < 1) :
    Valued.v (w * (algebraMap K₀ K (m 1 0) * u + algebraMap K₀ K (m 1 1)) -
      (algebraMap K₀ K (m 0 0) * u + algebraMap K₀ K (m 0 1))) = 1 := by sorry
