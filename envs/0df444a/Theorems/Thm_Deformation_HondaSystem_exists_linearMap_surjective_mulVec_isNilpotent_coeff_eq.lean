-- Prove2me | Theorems.Thm_Deformation_HondaSystem_exists_linearMap_surjective_mulVec_isNilpotent_coeff_eq
-- name    : Deformation.HondaSystem.exists_linearMap_surjective_mulVec_isNilpotent_coeff_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/7330c963-17a3-528f-9476-10fc13e52c79
-- title:
--   Fontaine's linear parts λ₀,λ₁ with nilpotent C
-- statement:
--   Let $\mathcal{O}$ be a commutative ring, $p$ a prime with $p$ a non-zero-divisor in $\mathcal{O}$, and suppose $\mathbb{Z}/p$ is an $\mathcal{O}$-algebra whose structure map has kernel $(p)$, with $\mathcal{O}$ complete for the $(p)$-adic topology. Let $r\in\mathbb{N}$ and let $H_1$ be a Honda system for $(p:\mathcal{O})$ on $\mathcal{O}^r$: $\mathcal{O}$-linear $F,V$ with $F\circ V=V\circ F=p\cdot\mathrm{id}$, together with a submodule $L$ such that every element of $L\cap\operatorname{range}F$ is $p$ times an element of $L$, $pL\subseteq\operatorname{range}F$, $\operatorname{range}F+L=\top$, and $V$ is injective on $L$. Let $G_v$ ($v\in\mathbb{N}$) be commutative rings, finite cocommutative Hopf algebras over $\mathbb{Z}/p$, with surjective coalgebra–algebra maps $s_v:G_{v+1}\to G_v$, $\dim G_v=p^{vr}$, $\ker s_v$ the image of the augmentation ideal of $G_{v+1}$ under multiplication by $p^v$, and each Cartier dual $\operatorname{CartierDual}(\mathbb{Z}/p,G_v)$ a local ring. Let $\pi_v:\mathcal{O}^r\to M(G_v)$ be surjective additive maps into the Dieudonné modules (colimits of the groups of comultiplicative truncated Witt vectors), with $\pi_v x=0$ exactly when $x\in p^v\mathcal{O}^r$, intertwining $F,V$ with Frobenius and Verschiebung and compatible with the maps induced by $s_v$. At level $1$ fix a splitting: finite cocommutative Hopf algebras $G^c_1,G^e_1$ over $\mathbb{Z}/p$ with $G^c_1$ local and $G^e_1$ reduced, maps $q^c_1:G_1\to G^c_1$ surjective, $\pi^e_1:G_1\to G^e_1$, and $\Theta_1:G_1\to G^c_1\otimes G^e_1$ bijective with $\Theta_1=(q^c_1\otimes\pi^e_1)\circ\Delta$. Finally fix $d\in\mathbb{N}$ and a surjective $\mathbb{Z}/p$-algebra map $\kappa_1:(\mathbb{Z}/p)[[X_1,\dots,X_d]]\to G^c_1$ with $\kappa_1(X_i)$ killed by the counit, $\ker\kappa_1\subseteq(X)^2$, and $d$ the $\mathbb{Z}/p$-dimension of the cotangent module of the augmentation ideal of $G^c_1$. Then there exist $\mathcal{O}$-linear $\lambda_0,\lambda_1:L\to(\mathbb{Z}/p)^d$ and $C\in M_d(\mathbb{Z}/p)$ such that $L$ is free and finite over $\mathcal{O}$ of rank $d$, $\lambda_0$ is surjective, $\lambda_0 m=0$ implies $m\in(p)\cdot L$, $C$ is nilpotent, $\lambda_1 m=C\,\lambda_0 m$ for all $m$, and $\lambda_0,\lambda_1$ compute the linear coefficients of the last two connected covector coordinates: for $l\in L$, $n\in\mathbb{N}$ and $u$ a comultiplicative truncated Witt vector of length $n+1$ over $G^c_1$ whose class in the Dieudonné module of $G^c_1$ is the image of $\pi_1 l$ under $q^c_1$, every power series $f$ with zero constant term and $\kappa_1 f=u_n$ satisfies $\operatorname{coeff}_{X_j}f=\lambda_0(l)_j$ for all $j$; and for $u$ of length $n+2$ with the same class, every such $f$ with $\kappa_1 f=u_n$ (the penultimate coordinate) satisfies $\operatorname{coeff}_{X_j}f=\lambda_1(l)_j$.
--
--   This is the set-up part of Fontaine's Lemme 1.5 in his classification of $p$-divisible groups by Honda systems: given a unipotent $p$-divisible tower with a Honda-system presentation, a connected–étale splitting at level $1$ and formal coordinates on the connected part, the last two covector coordinates of the points of $L$ have linear parts $\lambda_0$ and $\lambda_1=C\lambda_0$ with $C$ nilpotent, and $L$ is free of rank equal to the embedding dimension. It feeds the normal-form statement [`Deformation.HondaSystem.exists_mvFormalGroup_basis_coeff_eq_normalForm`](thm.html#Deformation.HondaSystem.exists_mvFormalGroup_basis_coeff_eq_normalForm), where a basis of $L$ adapted to $C$ is used to write down the formal group law.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_HondaSystem_exists_linearMap_surjective_mulVec_isNilpotent_coeff_eq.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_PDivisibleGroup_Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct
open MvPowerSeries

universe u v

theorem Deformation.HondaSystem.exists_linearMap_surjective_mulVec_isNilpotent_coeff_eq
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (r : ℕ) (H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞))
    (G : ℕ → Type v) [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)]
    (s : ∀ v, G (v + 1) →ₐc[ZMod p] G v) (hs : ∀ v, Function.Surjective (s v))
    (hrankG : ∀ v, Module.finrank (ZMod p) (G v) = p ^ (v * r))
    (hkerG : ∀ v, RingHom.ker (s v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (G (v + 1)) (p ^ v))
    (hunipG : ∀ v, IsLocalRing (CartierDual (ZMod p) (G v)))
    (π : ∀ v, (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (G v))
    (hπ : ∀ v, Function.Surjective (π v))
    (hπker : ∀ v x, π v x = 0 ↔ ∃ y, x = (p : 𝓞) ^ v • y)
    (hπF : ∀ v x, π v (H₁.F x) = Deformation.DieudonneModule.frobenius (ZMod p) p (G v) (π v x))
    (hπV : ∀ v x, π v (H₁.V x) = Deformation.DieudonneModule.verschiebung (ZMod p) p (G v) (π v x))
    (hπs : ∀ v x, Deformation.DieudonneModule.map (ZMod p) p (s v) (π (v + 1) x) = π v x)
    (Gc₁ Ge₁ : Type v) [CommRing Gc₁] [HopfAlgebra (ZMod p) Gc₁] [Coalgebra.IsCocomm (ZMod p) Gc₁]
    [Module.Finite (ZMod p) Gc₁] [CommRing Ge₁] [HopfAlgebra (ZMod p) Ge₁] [Coalgebra.IsCocomm (ZMod p) Ge₁]
    [Module.Finite (ZMod p) Ge₁]
    (qc₁ : G 1 →ₐc[ZMod p] Gc₁) (πe₁ : G 1 →ₐc[ZMod p] Ge₁) (Θ₁ : G 1 →ₐc[ZMod p] Gc₁ ⊗[ZMod p] Ge₁)
    (hGc₁ : IsLocalRing Gc₁) (hGe₁ : IsReduced Ge₁) (hqc₁ : Function.Surjective qc₁)
    (hΘ₁ : Function.Bijective Θ₁)
    (hΘ₁apply : ∀ b, Θ₁ b = Algebra.TensorProduct.map (qc₁ : G 1 →ₐ[ZMod p] Gc₁) (πe₁ : G 1 →ₐ[ZMod p] Ge₁)
      (Coalgebra.comul (R := ZMod p) b))
    {d : ℕ} (κ₁ : MvPowerSeries (Fin d) (ZMod p) →ₐ[ZMod p] Gc₁) (hκ₁ : Function.Surjective κ₁)
    (hκ₁ε : ∀ i, Coalgebra.counit (R := ZMod p) (κ₁ (X i)) = 0)
    (hκ₁ker : RingHom.ker κ₁ ≤ (Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) (ZMod p)))) ^ 2)
    (hd : d = Module.finrank (ZMod p) (PDivisibleGroup.Hopf.augIdeal (ZMod p) Gc₁).Cotangent) :
    ∃ (lam₀ lam₁ : H₁.L →ₗ[𝓞] (Fin d → ZMod p)) (C : Matrix (Fin d) (Fin d) (ZMod p)),
      Module.Free 𝓞 H₁.L ∧ Module.Finite 𝓞 H₁.L ∧ Module.finrank 𝓞 H₁.L = d ∧
      Function.Surjective lam₀ ∧
      (∀ m : H₁.L, lam₀ m = 0 → m ∈ Ideal.span {(p : 𝓞)} • (⊤ : Submodule 𝓞 H₁.L)) ∧
      IsNilpotent C ∧ (∀ m, lam₁ m = C.mulVec (lam₀ m)) ∧
      (∀ (l : H₁.L) (n : ℕ) (u : Deformation.wittHom (ZMod p) p (n + 1) Gc₁),
        Deformation.DieudonneModule.of (ZMod p) p Gc₁ (n + 1) u =
          Deformation.DieudonneModule.map (ZMod p) p qc₁ (π 1 ((l : H₁.L) : Fin r → 𝓞)) →
        ∀ f : MvPowerSeries (Fin d) (ZMod p), MvPowerSeries.constantCoeff f = 0 →
          κ₁ f = (u : TruncatedWittVector p (n + 1) Gc₁).coeff (Fin.last n) →
          ∀ j, MvPowerSeries.coeff (Finsupp.single j 1) f = lam₀ l j) ∧
      (∀ (l : H₁.L) (n : ℕ) (u : Deformation.wittHom (ZMod p) p (n + 2) Gc₁),
        Deformation.DieudonneModule.of (ZMod p) p Gc₁ (n + 2) u =
          Deformation.DieudonneModule.map (ZMod p) p qc₁ (π 1 ((l : H₁.L) : Fin r → 𝓞)) →
        ∀ f : MvPowerSeries (Fin d) (ZMod p), MvPowerSeries.constantCoeff f = 0 →
          κ₁ f = (u : TruncatedWittVector p (n + 2) Gc₁).coeff ⟨n, by omega⟩ →
          ∀ j, MvPowerSeries.coeff (Finsupp.single j 1) f = lam₁ l j) := by sorry
