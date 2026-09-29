-- Prove2me | Theorems.Thm_Deformation_DieudonneDatum_exists_pDivisibleTower_zmod_dieudonneModule_of_range_pow_le
-- name    : Deformation.DieudonneDatum.exists_pDivisibleTower_zmod_dieudonneModule_of_range_pow_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/f0cd751d-a292-5e42-a419-d8d2c646a0dd
-- title:
--   Realising a Dieudonné datum by a p-divisible tower over Fₚ
-- statement:
--   Let $\mathcal{O}$ be a commutative ring and $p$ a prime such that $p$ is a non-zero-divisor in $\mathcal{O}$, and suppose $\mathbf{F}_p =$ `ZMod p` is given as an $\mathcal{O}$-algebra whose structure map has kernel exactly the ideal $(p)$ of $\mathcal{O}$. Let $r \in \mathbb{N}$ and let $D_1$ be a `DieudonneDatum` with parameter $p$ on the free module $\mathcal{O}^r = (\mathrm{Fin}\,r \to \mathcal{O})$, that is, a pair of $\mathcal{O}$-linear endomorphisms $F, V$ of $\mathcal{O}^r$ with $F \circ V = V \circ F = p \cdot \mathrm{id}$, and assume that $V$ is topologically nilpotent in the sense that $V^N(\mathcal{O}^r) \subseteq p\,\mathcal{O}^r$ for some $N$. Then there is a family of types $G(v)$, $v \in \mathbb{N}$, each carrying a commutative ring structure, a Hopf algebra structure over $\mathbf{F}_p$ which is cocommutative as a coalgebra and finite as an $\mathbf{F}_p$-module, together with coalgebra-and-algebra homomorphisms $s_v \colon G(v+1) \to G(v)$ such that: each $s_v$ is surjective; $\dim_{\mathbf{F}_p} G(v) = p^{vr}$; the kernel of $s_v$ is the ideal [`PDivisibleGroup.Hopf.torsionIdeal`](def/PDivisibleGroup_Basic.html#L157) of $G(v+1)$ at $p^v$, namely the image of the augmentation ideal under the $p^v$-fold multiplication map; and each Cartier dual $\mathrm{Hom}_{\mathbf{F}_p}(G(v), \mathbf{F}_p)$ is a local ring. Moreover there are additive maps $\pi_v \colon \mathcal{O}^r \to \mathbb{D}(G(v))$, where $\mathbb{D}(A) = \varinjlim_n \mathrm{wittHom}(A)_n$ denotes the direct limit over $n$ of the groups of primitive elements of the truncated Witt vectors $W_n(A)$ along the shift maps, such that each $\pi_v$ is surjective, $\pi_v(x) = 0$ if and only if $x \in p^v\,\mathcal{O}^r$, $\pi_v$ carries $F$ to the Frobenius and $V$ to the Verschiebung of $\mathbb{D}(G(v))$, and $\mathbb{D}(s_v) \circ \pi_{v+1} = \pi_v$.
--
--   This is the object half (essential surjectivity) of the classical Dieudonné–Gabriel classification of unipotent $p$-divisible groups over the prime field $\mathbf{F}_p$ by finitely generated free Dieudonné modules with topologically nilpotent Verschiebung, formulated level by level in terms of the coordinate Hopf algebras: the data produced is exactly that of a [`PDivisibleGroup`](def/PDivisibleGroup_Basic.html#L199) over $\mathbf{F}_p$ of height $r$ (freeness over a field being automatic), together with a compatible identification of its Dieudonné modules with the reductions $\mathcal{O}^r/p^v\mathcal{O}^r$. It is used by [`Deformation.HondaSystem.exists_pDivisibleTower_dieudonneModule_of_range_pow_le`](thm.html#Deformation.HondaSystem.exists_pDivisibleTower_dieudonneModule_of_range_pow_le), where a Honda system over a base is reduced to its special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_DieudonneDatum_exists_pDivisibleTower_zmod_dieudonneModule_of_range_pow_le.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_PDivisibleGroup_Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem Deformation.DieudonneDatum.exists_pDivisibleTower_zmod_dieudonneModule_of_range_pow_le
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    (r : ℕ) (D₁ : Deformation.DieudonneDatum (p : 𝓞) (Fin r → 𝓞))
    (hV : ∃ N : ℕ, ∀ x, ∃ y, (D₁.V ^ N) x = (p : 𝓞) • y) :
    ∃ (G : ℕ → Type) (_ : ∀ v, CommRing (G v)) (_ : ∀ v, HopfAlgebra (ZMod p) (G v))
      (_ : ∀ v, Coalgebra.IsCocomm (ZMod p) (G v)) (_ : ∀ v, Module.Finite (ZMod p) (G v))
      (s : ∀ v, G (v + 1) →ₐc[ZMod p] G v),
      (∀ v, Function.Surjective (s v)) ∧ (∀ v, Module.finrank (ZMod p) (G v) = p ^ (v * r)) ∧
      (∀ v, RingHom.ker (s v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (G (v + 1)) (p ^ v)) ∧
      (∀ v, IsLocalRing (CartierDual (ZMod p) (G v))) ∧
    ∃ π : ∀ v, (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (G v),
      (∀ v, Function.Surjective (π v)) ∧
      (∀ v x, π v x = 0 ↔ ∃ y, x = (p : 𝓞) ^ v • y) ∧
      (∀ v x, π v (D₁.F x) = Deformation.DieudonneModule.frobenius (ZMod p) p (G v) (π v x)) ∧
      (∀ v x, π v (D₁.V x) = Deformation.DieudonneModule.verschiebung (ZMod p) p (G v) (π v x)) ∧
      (∀ v x, Deformation.DieudonneModule.map (ZMod p) p (s v) (π (v + 1) x) = π v x) := by sorry
