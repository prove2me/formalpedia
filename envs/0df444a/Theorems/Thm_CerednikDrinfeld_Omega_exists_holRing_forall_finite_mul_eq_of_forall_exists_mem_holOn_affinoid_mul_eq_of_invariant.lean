-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_holRing_forall_finite_mul_eq_of_forall_exists_mem_holOn_affinoid_mul_eq_of_invariant
-- name    : CerednikDrinfeld.Omega.exists_holRing_forall_finite_mul_eq_of_forall_exists_mem_holOn_affinoid_mul_eq_of_invariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/58bd5f24-9f88-5df0-b18a-3871b6f350a4
-- title:
--   Invariant chartwise meromorphic functions on Ω are quotients
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K_0$, let $\varpi\in R$ be irreducible with $R/(\varpi)$ finite, and let $K$ be a field extension of $K_0$ carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, complete and algebraically closed. Assume: $v$ is $\le 1$ on the image of $R$; every $a\in K_0$ with $v(a)\le 1$ is an integer of $R$ in the localisation sense; the powers $v(\varpi)^N$ are cofinal downwards in $\Gamma_0\setminus\{0\}$; and the rank-one condition that for $v(x)<1$ and $y\ne 0$ some $v(x)^n\le v(y)$. Let $\varpi_1$ be a pseudo-uniformiser (an element of $K_0$ of valuation in $(0,1)$ whose powers bound the valuation of every nonzero element of $K_0$ above and below) whose affinoids $\Omega_n=$ `affinoid` $\varpi_1\,n$ exhaust the Drinfeld upper half-plane $\Omega=K\setminus\mathrm{image}(K_0)$, and assume the ring `holRing` $\varpi_1$ of functions on $\Omega$ holomorphic on every $\Omega_n$ (uniform limits on $\Omega_n$ of uniformly bounded sequences of rational functions without poles there) is a domain. Let $G$ be a group with a homomorphism $\rho : G \to \mathrm{PGL}_2(K_0)$ and an action on the set of homothety classes of full lattices in $K_0^2$ which preserves adjacency in the Bruhat–Tits tree, which agrees with the action through $\rho$, which has finite vertex stabilisers and finitely many vertex orbits, and which admits a $G$-invariant map $\tau$ to $\mathbb{Z}/2$ taking distinct values on adjacent vertices. Let $F : \Omega\to K$ satisfy $F(w)=F(z)$ whenever $w$ is the image of $z$ under the Möbius action of $\rho(\gamma)$, $\gamma\in G$, and assume that for each $n$ there are $f,g$ holomorphic on $\Omega_n$ with $g$ not identically zero and $g(z)F(z)=f(z)$ at every $z\in\Omega_n$ with $g(z)\ne 0$. Then there are $\Phi, H \in$ `holRing` $\varpi_1$ with $H\ne 0$ such that for every $n$ there is a finite subset $Z\subseteq\Omega_n$ with $H(z)F(z)=\Phi(z)$ for all $z\in\Omega_n\setminus Z$.
--
--   This is the statement that a $\rho(G)$-invariant function on Drinfeld's upper half-plane which is meromorphic on each affinoid of the exhaustion is, generically on each affinoid, a quotient $\Phi/H$ of two global holomorphic functions, i.e. lies in the fraction field of the ring of holomorphic functions on $\Omega$; the exceptional set is only required to be finite on each affinoid, since $F$ is a bare function and its values at removable points are not constrained by the hypothesis. It is used by [`CerednikDrinfeld.exists_holRing_forall_finite_mul_eq_of_invariant_of_cerednikDrinfeld_group`](thm.html#CerednikDrinfeld.exists_holRing_forall_finite_mul_eq_of_invariant_of_cerednikDrinfeld_group), where the discreteness and colouring hypotheses are supplied by the group occurring in the Čerednik–Drinfeld uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_holRing_forall_finite_mul_eq_of_forall_exists_mem_holOn_affinoid_mul_eq_of_invariant.lean

import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Omega.exists_holRing_forall_finite_mul_eq_of_forall_exists_mem_holOn_affinoid_mul_eq_of_invariant
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ ε)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (ϖ₁ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ₁) [IsDomain ↥(holRing ϖ₁)]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀))
    [MulAction G (LT.LatticeTree.Vertex R K₀)]
    [CerednikDrinfeld.Mumford.GraphAction G (CerednikDrinfeld.BruhatTits.tree R K₀)]
    (hρ : CerednikDrinfeld.Mumford.ActsThrough (LT.LatticeTree.Vertex R K₀) ρ)

    (hfin : ∀ w : LT.LatticeTree.Vertex R K₀, Finite (MulAction.stabilizer G w))
    [Finite (CerednikDrinfeld.Mumford.QuotVert G (LT.LatticeTree.Vertex R K₀))]

    (τ : LT.LatticeTree.Vertex R K₀ → ZMod 2) (hτ : ∀ (g : G) (w : LT.LatticeTree.Vertex R K₀), τ (g • w) = τ w)
    (hadj : ∀ u w : LT.LatticeTree.Vertex R K₀, (CerednikDrinfeld.BruhatTits.tree R K₀).Adj u w → τ u ≠ τ w)

    (F : ↥(upperHalfPlane K₀ K) → K)
    (hinv : ∀ (γ : G) (z w : ↥(upperHalfPlane K₀ K)), (w : K) = pmoebius K₀ (ρ γ) (z : K) → F w = F z)
    (hmer : ∀ n : ℕ, ∃ f g : ↥(affinoid ϖ₁ n) → K, f ∈ holOn K (affinoid ϖ₁ n) ∧ g ∈ holOn K (affinoid ϖ₁ n) ∧
      (∃ z : ↥(affinoid ϖ₁ n), g z ≠ 0) ∧
      ∀ z : ↥(affinoid ϖ₁ n), g z ≠ 0 →
        g z * F ⟨(z : K), affinoid_subset_upperHalfPlane ϖ₁ n z.2⟩ = f z) :
    ∃ Φ H : ↥(holRing ϖ₁), H ≠ 0 ∧
      ∀ n : ℕ, ∃ Z : Set ↥(affinoid ϖ₁ n), Z.Finite ∧
        ∀ z : ↥(affinoid ϖ₁ n), z ∉ Z →
          (H : ↥(upperHalfPlane K₀ K) → K) ⟨(z : K), affinoid_subset_upperHalfPlane ϖ₁ n z.2⟩ *
              F ⟨(z : K), affinoid_subset_upperHalfPlane ϖ₁ n z.2⟩ =
            (Φ : ↥(upperHalfPlane K₀ K) → K) ⟨(z : K), affinoid_subset_upperHalfPlane ϖ₁ n z.2⟩ := by sorry
