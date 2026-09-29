-- Prove2me | Theorems.Thm_Deformation_HondaSystem_map_eq_zero_of_mem_of_isCompl_of_bijective_tensorProduct
-- name    : Deformation.HondaSystem.map_eq_zero_of_mem_of_isCompl_of_bijective_tensorProduct
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/76551eae-9553-5032-b6f0-b312859b7e8a
-- title:
--   Fitting summands of a Honda system and the connected–étale splitting
-- statement:
--   Let $\mathcal O$ be a commutative ring, $p$ a prime such that $p$ is a non-zero-divisor in $\mathcal O$, equipped with an $\mathcal O$-algebra structure on $\mathbb Z/p$ whose structure map has kernel exactly the ideal $(p)$, and with $\mathcal O$ adically complete for $(p)$. Fix $r$ and a Honda system $H_1$ for the element $p$ on $\mathcal O^r=(\mathrm{Fin}\,r\to\mathcal O)$, that is, $\mathcal O$-linear endomorphisms $F,V$ of $\mathcal O^r$ with $F\circ V=V\circ F=p\cdot\mathrm{id}$ together with a submodule $L$ satisfying the Honda axioms ($x\in L\cap\operatorname{range}F$ implies $x=p y$ for some $y\in L$; $p y\in\operatorname{range}F$ for $y\in L$; $\operatorname{range}F+L=\top$; $V$ injective on $L$). Let $G:\mathbb N\to\mathrm{Type}$ be a family of finite cocommutative Hopf algebras over $\mathbb Z/p$ with transition maps $s_v\colon G(v+1)\to G(v)$ of algebra-and-coalgebra homomorphisms, and let $\pi_v\colon\mathcal O^r\to M(G(v))$ be additive maps into the Dieudonné modules $M(A)=\varinjlim_n\{x\in \mathbb W_n(A):\Delta x=x\otimes 1+1\otimes x\}$, assumed surjective, with $\pi_v x=0$ iff $x\in p^v\mathcal O^r$, intertwining $F$ with the Witt-vector Frobenius on $M(G(v))$, and compatible with the transitions via $M(s_v)$. Fix a level $v$, finite cocommutative Hopf algebras $G^c,G^e$ over $\mathbb Z/p$, algebra-and-coalgebra maps $q^c\colon G(v)\to G^c$, $\pi^e\colon G(v)\to G^e$ and $\Theta\colon G(v)\to G^c\otimes_{\mathbb Z/p}G^e$, with $\Theta$ bijective and $\Theta b=(q^c\otimes\pi^e)(\Delta b)$ for all $b$, where $G^c$ is a local ring and $G^e$ is reduced. Finally let $M^c,M^{\mathrm{et}}\subseteq\mathcal O^r$ be submodules characterised by: $m\in M^{\mathrm{et}}$ iff $m\in\operatorname{range}(F^N)$ for every $N$; and $m\in M^c$ iff for every $k$ there is $N$ with $F^N m\in p^k\mathcal O^r$. The conclusion is the conjunction: $M(\pi^e)(\pi_v m)=0$ for all $m\in M^c$, and $M(q^c)(\pi_v m)=0$ for all $m\in M^{\mathrm{et}}$.
--
--   This expresses the compatibility of the slope (Fitting) decomposition of a Honda system with the connected–étale splitting of the finite group schemes in the associated tower: the connected summand is carried into the Dieudonné module of the local factor and the unit-root summand into that of the reduced factor. It feeds the construction of split coordinates and normal forms for Honda systems, and the rank computation attached to the splitting, via [`Deformation.HondaSystem.exists_splitCoordinates_lawful_normalForm`](thm.html#Deformation.HondaSystem.exists_splitCoordinates_lawful_normalForm) and [`Deformation.HondaSystem.finrank_eq_of_isCompl_of_bijective_tensorProduct_comul`](thm.html#Deformation.HondaSystem.finrank_eq_of_isCompl_of_bijective_tensorProduct_comul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_HondaSystem_map_eq_zero_of_mem_of_isCompl_of_bijective_tensorProduct.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

universe u v

theorem Deformation.HondaSystem.map_eq_zero_of_mem_of_isCompl_of_bijective_tensorProduct
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (r : ℕ) (H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞))
    (G : ℕ → Type v) [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)]
    (s : ∀ v, G (v + 1) →ₐc[ZMod p] G v)
    (π : ∀ v, (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (G v))
    (hπ : ∀ v, Function.Surjective (π v))
    (hπker : ∀ v x, π v x = 0 ↔ ∃ y, x = (p : 𝓞) ^ v • y)
    (hπF : ∀ v x, π v (H₁.F x) = Deformation.DieudonneModule.frobenius (ZMod p) p (G v) (π v x))
    (hπs : ∀ v x, Deformation.DieudonneModule.map (ZMod p) p (s v) (π (v + 1) x) = π v x)
    (v : ℕ)
    (Gc Ge : Type v) [CommRing Gc] [HopfAlgebra (ZMod p) Gc] [Coalgebra.IsCocomm (ZMod p) Gc]
    [Module.Finite (ZMod p) Gc] [CommRing Ge] [HopfAlgebra (ZMod p) Ge] [Coalgebra.IsCocomm (ZMod p) Ge]
    [Module.Finite (ZMod p) Ge]
    (qc : G v →ₐc[ZMod p] Gc) (πe : G v →ₐc[ZMod p] Ge) (Θ : G v →ₐc[ZMod p] Gc ⊗[ZMod p] Ge)
    (hΘ : Function.Bijective Θ)
    (hΘapply : ∀ b, Θ b = Algebra.TensorProduct.map (qc : G v →ₐ[ZMod p] Gc) (πe : G v →ₐ[ZMod p] Ge)
      (Coalgebra.comul (R := ZMod p) b))
    (hGc : IsLocalRing Gc) (hGe : IsReduced Ge)
    (Mc Met : Submodule 𝓞 (Fin r → 𝓞))
    (hMet : ∀ m, m ∈ Met ↔ ∀ N : ℕ, ∃ y, (H₁.F ^ N) y = m)
    (hMc : ∀ m, m ∈ Mc ↔ ∀ k : ℕ, ∃ N : ℕ, ∃ y, (H₁.F ^ N) m = (p : 𝓞) ^ k • y) :
    (∀ m ∈ Mc, Deformation.DieudonneModule.map (ZMod p) p πe (π v m) = 0) ∧
    (∀ m ∈ Met, Deformation.DieudonneModule.map (ZMod p) p qc (π v m) = 0) := by sorry
