-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordTower_exists_monoidHom_aut_forall_q_eq_q_comp_of_le
-- name    : CerednikDrinfeld.FormalOmega.MumfordTower.exists_monoidHom_aut_forall_q_eq_q_comp_of_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/ca10102d-5eeb-58b4-a41b-6ecf8874c936
-- title:
--   Γ-action on a Mumford tower when Ntrianglelefteqρ(Γ)
-- statement:
--   Fix a commutative ring $\mathcal O$, an element $\pi\in\mathcal O$, a field $K_0$ that is an $\mathcal O$-algebra, a natural number $r$, a matrix $g_1\in\mathrm{GL}_2(K_0)$, a group $G$, a homomorphism $\sigma:G\to\mathrm{GL}_2(K_0)$, a subgroup $\Gamma\le G$, a homomorphism $\rho:G\to\mathrm{PGL}_2(K_0)$ with $\rho(g)$ equal to the class of $\sigma(g)$ for every $g\in G$, and a subgroup $N\le\mathrm{PGL}_2(K_0)$ with $N\le\rho(\Gamma)$ and with $N$, viewed inside $\rho(\Gamma)$, normal there. Let $D$ be a `MumfordTower` for these data: schemes $Z_n$ with structure morphisms $\mathrm{zb}_n:Z_n\to\operatorname{Spec}(\mathcal O/\pi^{n+1})$, transition maps $\mathrm{zt}_n:Z_n\to Z_{n+1}$, and for each $\mathcal O$-algebra $B$ with $\pi^{n+1}=0$ in $B$ a map $q_n$ sending a Deligne datum $P\in(\mathrm{Omega}\,K_0\,\pi)(B)$ to a morphism $\operatorname{Spec}B\to Z_n$. The assertion is the existence of homomorphisms $\mathrm{act}_n:\Gamma\to\operatorname{Aut}(Z_n)$, one for each $n$, such that: (i) $\mathrm{act}_n(\gamma)$ followed by $\mathrm{zb}_n$ equals $\mathrm{zb}_n$; (ii) $\mathrm{zt}_n$ followed by $\mathrm{act}_{n+1}(\gamma)$ equals $\mathrm{act}_n(\gamma)$ followed by $\mathrm{zt}_n$; (iii) $\mathrm{act}_n(\gamma)$ is the identity of $Z_n$ whenever $\rho(\gamma)\in N$; and (iv) for all $n$, $\gamma\in\Gamma$, $\mathcal O$-algebras $B$ with $\pi^{n+1}=0$ in $B$, and Deligne data $P,P'$ over $B$ satisfying $\mathrm{DeligneDatum.IsPullback}$ for $\sigma(\gamma)^{-1}$, i.e. $P'.\mathrm{line}(M)$ is the preimage of $P.\mathrm{line}(\sigma(\gamma)^{-1}M)$ under the base-changed action isomorphism, for every full lattice $M$, one has $q_n(P')=q_n(P)$ followed by $\mathrm{act}_n(\gamma)$.
--
--   This packages the Čerednik–Drinfeld descent datum: the action of an arithmetic group $\Gamma$ on the Mumford tower over $\operatorname{Spec}\mathcal O/\pi^{n+1}$ as genuine group homomorphisms into $\operatorname{Aut}(Z_n)$, compatible with the structure and transition morphisms, trivial on the part of $\Gamma$ mapping into $N$, and pinned down on the Deligne-datum charts. It feeds the construction of the twisted tower, [`CerednikDrinfeld.FormalOmega.MumfordTower.exists_twistedTower`](thm.html#CerednikDrinfeld.FormalOmega.MumfordTower.exists_twistedTower).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_MumfordTower_exists_monoidHom_aut_forall_q_eq_q_comp_of_le.lean

import Definitions.Def_CerednikDrinfeld_MumfordTower
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.MumfordTower.exists_monoidHom_aut_forall_q_eq_q_comp_of_le
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] (r : ℕ)
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀)
    (G : Type) [Group G] (σ : G →* Matrix.GeneralLinearGroup (Fin 2) K₀) (Γ : Subgroup G)
    (ρ : G →* PGL(2, K₀)) (hρ : ∀ g : G, ρ g = Matrix.ProjGenLinGroup.mk (σ g))
    (N : Subgroup (PGL(2, K₀))) (hNle : N ≤ Γ.map ρ) (hNnorm : (N.subgroupOf (Γ.map ρ)).Normal)
    (D : MumfordTower 𝒪 π K₀ r g₁ N) :
    ∃ act : ∀ n : ℕ, ↥Γ →* Aut (D.Z n),

      (∀ (n : ℕ) (γ : ↥Γ), (act n γ).hom ≫ D.zb n = D.zb n) ∧

      (∀ (n : ℕ) (γ : ↥Γ), D.zt n ≫ (act (n + 1) γ).hom = (act n γ).hom ≫ D.zt n) ∧

      (∀ (n : ℕ) (γ : ↥Γ), ρ (γ : G) ∈ N → (act n γ).hom = 𝟙 (D.Z n)) ∧

      (∀ (n : ℕ) (γ : ↥Γ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
        (P P' : (Omega K₀ π).obj B), DeligneDatum.IsPullback (K := K₀) (π := π) B (σ (γ : G))⁻¹ P P' →
        D.q n B hB P' = D.q n B hB P ≫ (act n γ).hom) := by sorry
