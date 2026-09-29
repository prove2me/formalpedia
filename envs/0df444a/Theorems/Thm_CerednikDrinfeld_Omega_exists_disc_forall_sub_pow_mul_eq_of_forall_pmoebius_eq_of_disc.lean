-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_disc_forall_sub_pow_mul_eq_of_forall_pmoebius_eq_of_disc
-- name    : CerednikDrinfeld.Omega.exists_disc_forall_sub_pow_mul_eq_of_forall_pmoebius_eq_of_disc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/d4685457-06ba-5beb-9d9b-645ef0eca9cd
-- title:
--   Transporting a local presentation of an invariant function along ρ(γ)
-- statement:
--   Let $K_0$ be a field and $K$ a complete, algebraically closed field with a valuation $v$ taking values in a linearly ordered commutative group with zero, together with a $K_0$-algebra structure; let $\varpi$ be a pseudo-uniformizer, i.e. an element of $K_0$ whose image has valuation in $(0,1)$ and such that every nonzero element of $K_0$ has valuation between $v(\varpi)^N$ and $v(\varpi)^{-N}$ for some $N$, and assume the rank-one hypothesis that for $x,y \in K$ with $v(x)<1$ and $y \neq 0$ one has $v(x)^n \le v(y)$ for some $n$. Let $\rho : G \to \mathrm{PGL}_2(K_0)$ be a homomorphism from a group $G$, and let $F$ be a $K$-valued function on the Drinfeld upper half-plane $\Omega = K \setminus \mathrm{im}(K_0 \to K)$ which is $\rho$-invariant: $F(w) = F(z)$ whenever $z,w \in \Omega$ and $w = \mathrm{pmoebius}(\rho\gamma)(z)$, the fractional-linear action of $\rho\gamma$ on $\mathbb{P}^1(K)$ read in the affine coordinate. Fix $\gamma \in G$, natural numbers $m,n$, a point $p \in \Omega$ lying in the affinoid $\Omega_m$ (the set of $z$ with $v(z) \le v(\varpi)^{-m}$ and $v(z-a) \ge v(\varpi)^{m}$ for all $a \in K_0$ with $v(a) \le v(\varpi)^{-m}$), and put $q = \mathrm{pmoebius}(\rho\gamma)(p)$. Let $s \neq 0$ be such that the closed disc $E = \{w : v(w-q) \le v(s)\}$ is contained in $\Omega_n$, and let $\varphi : E \to K$ lie in the subring $\mathrm{holOn}(E)$ of functions that are uniform limits of rational functions pole-free on $E$ with values uniformly bounded in valuation. Let $e \in \mathbb{N}$ with $e = 0$ or $\varphi(q) \neq 0$, and suppose $(w-q)^e F(w) = \varphi(w)$ for all $w \in E$ with $w \neq q$. The conclusion is that there exists $r \neq 0$ in $K$ such that the closed disc $D = \{z : v(z-p) \le v(r)\}$ is contained in $\Omega_m$, together with a function $\varphi' \in \mathrm{holOn}(D)$ satisfying $e = 0$ or $\varphi'(p) \neq 0$, and $(z-p)^e F(z) = \varphi'(z)$ for all $z \in D$ with $z \neq p$.
--
--   This is the disc-to-disc transport step for invariant functions on Drinfeld's upper half-plane: a local presentation of $F$ with a pole of order at most $e$ at the image point $q = \rho(\gamma)p$, valid on a disc inside one affinoid, is carried back along the fractional-linear map to a presentation on a disc about $p$ inside the affinoid $\Omega_m$ containing $p$. It feeds the construction of the ring of invariant analytic functions, being used in [`CerednikDrinfeld.Omega.exists_holRing_forall_finite_mul_eq_of_forall_exists_mem_holOn_affinoid_mul_eq_of_invariant`](thm.html#CerednikDrinfeld.Omega.exists_holRing_forall_finite_mul_eq_of_forall_exists_mem_holOn_affinoid_mul_eq_of_invariant).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_disc_forall_sub_pow_mul_eq_of_forall_pmoebius_eq_of_disc.lean

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
open CerednikDrinfeld.Omega CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Omega.exists_disc_forall_sub_pow_mul_eq_of_forall_pmoebius_eq_of_disc
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀))
    (F : ↥(upperHalfPlane K₀ K) → K)
    (hinv : ∀ (γ : G) (z w : ↥(upperHalfPlane K₀ K)), (w : K) = pmoebius K₀ (ρ γ) (z : K) → F w = F z)
    (γ : G) (m n : ℕ) (p : ↥(upperHalfPlane K₀ K)) (hp : (p : K) ∈ affinoid ϖ m)
    (s : K) (hs : s ≠ 0)
    (hE : ∀ w : K, Valued.v (w - pmoebius K₀ (ρ γ) (p : K)) ≤ Valued.v s → w ∈ affinoid ϖ n)
    {φ : ↥{w : K | Valued.v (w - pmoebius K₀ (ρ γ) (p : K)) ≤ Valued.v s} → K}
    (hφ : φ ∈ holOn K {w : K | Valued.v (w - pmoebius K₀ (ρ γ) (p : K)) ≤ Valued.v s}) (e : ℕ)
    (he : e = 0 ∨ φ ⟨pmoebius K₀ (ρ γ) (p : K), by simp⟩ ≠ 0)
    (h : ∀ w : ↥{w : K | Valued.v (w - pmoebius K₀ (ρ γ) (p : K)) ≤ Valued.v s},
      (w : K) ≠ pmoebius K₀ (ρ γ) (p : K) →
      ((w : K) - pmoebius K₀ (ρ γ) (p : K)) ^ e *
          F ⟨(w : K), affinoid_subset_upperHalfPlane ϖ n (hE (w : K) w.2)⟩ = φ w) :
    ∃ r : K, r ≠ 0 ∧ ∃ hD : (∀ z : K, Valued.v (z - (p : K)) ≤ Valued.v r → z ∈ affinoid ϖ m),
      ∃ φ' : ↥{z : K | Valued.v (z - (p : K)) ≤ Valued.v r} → K,
        φ' ∈ holOn K {z : K | Valued.v (z - (p : K)) ≤ Valued.v r} ∧
        (e = 0 ∨ φ' ⟨(p : K), by simp⟩ ≠ 0) ∧
        ∀ z : ↥{z : K | Valued.v (z - (p : K)) ≤ Valued.v r}, (z : K) ≠ (p : K) →
          ((z : K) - (p : K)) ^ e *
              F ⟨(z : K), affinoid_subset_upperHalfPlane ϖ m (hD (z : K) z.2)⟩ = φ' z := by sorry
