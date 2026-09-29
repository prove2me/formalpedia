-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_eq_algebraMap_of_forall_smul_eq_of_forall_exists_smul_mem_affinoid
-- name    : CerednikDrinfeld.Omega.exists_eq_algebraMap_of_forall_smul_eq_of_forall_exists_smul_mem_affinoid
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/ca7b3536-d762-50bb-b1ba-28589460f099
-- title:
--   Liouville theorem for Λ-invariant functions on Ω
-- statement:
--   Let $K_0$ be a field and $K$ a $K_0$-algebra field carrying a valuation $v$ with values in a linearly ordered commutative group with zero, complete and algebraically closed. Let $\varpi$ be a pseudo-uniformiser: an element $\varpi \in K_0$ with $0 < v(\varpi) < 1$ in $K$ and such that every nonzero $a \in K_0$ satisfies $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$ for some $N \in \mathbb{N}$ (valuations of elements of $K_0$ are always taken after the structure map to $K$). Three hypotheses are imposed on the valued situation: a rank-one condition, that for all $x, y \in K$ with $v(x) < 1$ and $y \ne 0$ there is $n$ with $v(x)^n \le v(y)$; exhaustion, that every $z$ in the upper half-plane $\Omega = K \setminus \operatorname{range}(K_0 \to K)$ lies in some affinoid $\Omega_n = \{z : v(z) \le v(\varpi)^{-n}$ and $v(z - a) \ge v(\varpi)^{n}$ for all $a \in K_0$ with $v(a) \le v(\varpi)^{-n}\}$; and a local finiteness condition, that for each $n$ there is a finite set $T \subseteq K_0$ with every $a \in K_0$ satisfying $v(a) \le v(\varpi)^{-n}$ within distance $< v(\varpi)^{n}$ of some $t \in T$. Let $G$ be a group, $\rho : G \to \mathrm{PGL}_2(K_0)$ a homomorphism, $\Lambda \le G$ a subgroup and $N \in \mathbb{N}$ such that every $z \in \Omega$ admits $\gamma \in \Lambda$ with $\rho(\gamma) \cdot z \in \Omega_N$. Let $f$ belong to the ring of rigid-holomorphic functions on $\Omega$, i.e. functions $\Omega \to K$ whose restriction to each $\Omega_n$ is the uniform limit of a uniformly bounded sequence of rational functions without poles on $\Omega_n$, and assume $\rho(\gamma) \cdot f = f$ for all $\gamma \in \Lambda$. Then $f$ is the constant function attached to some $c \in K$, i.e. $f$ is the image of $c$ under the structure map $K \to \mathcal{O}(\Omega)$.
--
--   This is the Liouville theorem for Drinfeld's $p$-adic upper half-plane in the cocompact case: a rigid-holomorphic function invariant under a subgroup whose translates of a single affinoid cover $\Omega$ is constant. It is used in the study of the function field of the associated Mumford curve, for instance in the results deducing the hypothesis of orbit-meeting from finiteness of a quotient of vertices or from finiteness of a relative index.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_eq_algebraMap_of_forall_smul_eq_of_forall_exists_smul_mem_affinoid.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_eq_algebraMap_of_forall_smul_eq_of_forall_exists_smul_mem_affinoid
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hex : IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    (G : Type) [Group G] (ρ : G →* PGL(2, K₀)) (Λ : Subgroup G)
    (N : ℕ) (hcpt : ∀ z : ↥(upperHalfPlane K₀ K), ∃ γ ∈ Λ, ((ρ γ • z : ↥(upperHalfPlane K₀ K)) : K) ∈ affinoid ϖ N)
    (f : ↥(holRing ϖ)) (hinv : ∀ γ ∈ Λ, ρ γ • f = f) :
    ∃ c : K, f = algebraMap K ↥(holRing ϖ) c := by sorry
