-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_pow_le_v_phi_of_mem_affinoid_of_v_det_lt
-- name    : CerednikDrinfeld.Omega.pow_le_v_phi_of_mem_affinoid_of_v_det_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/706296f6-9482-510c-883e-ca89e1b8bb00
-- title:
--   Lower bound for z(cb+d)-(ab+β) on the affinoid Ωₙ
-- statement:
--   Let $K_0$ be a field, $K$ a field that is a $K_0$-algebra, and let $K$ carry a valuation $v =$ `Valued.v` with values in a linearly ordered commutative group with zero $\Gamma_0$. Let $\varpi$ be a pseudo-uniformiser, i.e. an element $\varpi \in K_0$ with $0 < v(\varpi) < 1$ in $K$ and such that every nonzero $a \in K_0$ satisfies $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$ for some $N \in \mathbb{N}$ (valuations of elements of $K_0$ are always taken after the structure map $K_0 \to K$); write $\mathfrak{p} = v(\varpi)$. Let $n \in \mathbb{N}$ and let $b, z \in K$ both lie in the $n$-th affinoid, that is $v(b) \le \mathfrak{p}^{-n}$ and $\mathfrak{p}^{n} \le v(b - a)$ for every $a \in K_0$ with $v(a) \le \mathfrak{p}^{-n}$, and likewise for $z$. Let $g$ be a $2 \times 2$ matrix over $K_0$ all of whose entries satisfy $v(g_{ij}) \le 1$, with $v(g_{ij}) = 1$ for at least one pair $(i,j)$, and whose determinant satisfies $v(\det g) < \mathfrak{p}^{6n}$. Then $$\mathfrak{p}^{4n} \le v\bigl(z\,(g_{10} b + g_{11}) - (g_{00} b + g_{01})\bigr).$$
--
--   This is the uniform quantitative statement that a unit-normalised integral $2\times 2$ matrix of nearly vanishing determinant cannot move a point of the affinoid $\Omega_n$ close to another such point: the numerator-type expression $z(cb+d)-(ab+\beta)$ attached to the Möbius action of $g$ stays bounded away from $0$. It underlies the discreteness and convergence estimates in this development, being used for the finiteness of the set of group elements carrying a point into an affinoid, for the normalisation $v(\Phi)=1$ in the unramified case, and for the cofinite convergence of the theta factors to $1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_pow_le_v_phi_of_mem_affinoid_of_v_det_lt.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.pow_le_v_phi_of_mem_affinoid_of_v_det_lt
    {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ : PseudoUniformizer K₀ K) (n : ℕ) {b z : K} (hb : b ∈ affinoid ϖ n) (hz : z ∈ affinoid ϖ n)
    (g : Matrix (Fin 2) (Fin 2) K₀)
    (hle : ∀ i j : Fin 2, Valued.v (algebraMap K₀ K (g i j)) ≤ 1)
    (hone : ∃ i j : Fin 2, Valued.v (algebraMap K₀ K (g i j)) = 1)
    (hdet : Valued.v (algebraMap K₀ K g.det) < Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (6 * n)) :
    Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (4 * n) ≤
      Valued.v (z * (algebraMap K₀ K (g 1 0) * b + algebraMap K₀ K (g 1 1)) -
        (algebraMap K₀ K (g 0 0) * b + algebraMap K₀ K (g 0 1))) := by sorry
