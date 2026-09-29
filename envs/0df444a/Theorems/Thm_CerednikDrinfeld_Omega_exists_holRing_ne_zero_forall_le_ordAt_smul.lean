-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_holRing_ne_zero_forall_le_ordAt_smul
-- name    : CerednikDrinfeld.Omega.exists_holRing_ne_zero_forall_le_ordAt_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/435fb857-93fe-5b50-80db-de6b40d341e7
-- title:
--   Holomorphic function vanishing to prescribed orders along G-orbits
-- statement:
--   Let $K_0$ be a field and $K$ a $K_0$-algebra which is a field, carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, complete and algebraically closed. Let $\varpi$ be a pseudo-uniformiser: an element $\varpi.\varpi \in K_0$ with $0 < v(\varpi.\varpi) < 1$ in $K$ such that every non-zero $a \in K_0$ satisfies $v(\varpi.\varpi)^N \le v(a) \le v(\varpi.\varpi)^{-N}$ for some $N \in \mathbb{N}$. Three further hypotheses are assumed: `hrk`, that for all $x, y \in K$ with $v(x) < 1$ and $y \ne 0$ there is $n$ with $v(x)^n \le v(y)$ (a rank-one, Archimedean condition on the value group); `hex`, that the sets $\mathrm{affinoid}\,\varpi\,n = \{z : v(z) \le v(\varpi.\varpi)^{-n} \text{ and } v(z - a) \ge v(\varpi.\varpi)^{n} \text{ for all } a \in K_0 \text{ with } v(a) \le v(\varpi.\varpi)^{-n}\}$ exhaust the Drinfeld upper half-plane $\Omega = K \setminus \mathrm{image}(K_0)$; and `hfin`, that for each $n$ there is a finite $T \subseteq K_0$ such that every $a \in K_0$ with $v(a) \le v(\varpi.\varpi)^{-n}$ satisfies $v(a - t) < v(\varpi.\varpi)^{n}$ for some $t \in T$ (finitely many holes at each level). Let $G$ be a group and $\rho : G \to \mathrm{PGL}_2(K_0)$ a homomorphism which is discrete in the sense that for every $\varepsilon \ne 0$ in $\Gamma_0$ only finitely many $\gamma \in G$ admit a lift $g \in \mathrm{GL}_2(K_0)$ of $\rho(\gamma)$ with all entries of valuation $\le 1$ and $v(\det g) \ge \varepsilon$. Finally let $\iota$ be a finite index type, $b : \iota \to \Omega$ a family of points and $m : \iota \to \mathbb{N}$ a family of multiplicities. The conclusion is that there exists a non-zero element $H$ of `holRing` $\varpi$ — the subring of functions $\Omega \to K$ whose restriction to each affinoid is a uniform limit of a uniformly bounded sequence of rational functions without poles there — such that for every $i \in \iota$ and every $\gamma \in G$ one has $m_i \le \mathrm{ord}_{\rho(\gamma) \cdot b_i} H$, where $\mathrm{ord}_z H$ is the supremum of the $n$ with $(\mathrm{coord} - z)^n \mid H$ in `holRing` $\varpi$.
--
--   This is the existence statement for products of theta functions $\Theta(b,b;\cdot)$ attached to a discrete subgroup of $\mathrm{PGL}_2(K_0)$ acting on Drinfeld's upper half-plane: a non-zero rigid-holomorphic function vanishing to at least prescribed order along each of finitely many orbits, with no automorphy asserted. It is used in the construction of $G$-invariant holomorphic data on $\Omega$, via [`CerednikDrinfeld.Omega.exists_holRing_forall_finite_mul_eq_of_forall_exists_mem_holOn_affinoid_mul_eq_of_invariant`](thm.html#CerednikDrinfeld.Omega.exists_holRing_forall_finite_mul_eq_of_forall_exists_mem_holOn_affinoid_mul_eq_of_invariant).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_holRing_ne_zero_forall_le_ordAt_smul.lean

import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_OmegaOrdAt
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega
open CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Omega.exists_holRing_ne_zero_forall_le_ordAt_smul
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hex : IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    {ι : Type} [Fintype ι] (b : ι → ↥(upperHalfPlane K₀ K)) (m : ι → ℕ) :
    ∃ H : ↥(holRing ϖ), H ≠ 0 ∧
      ∀ (i : ι) (γ : G), m i ≤ ordAt ϖ H (ρ γ • b i) := by sorry
