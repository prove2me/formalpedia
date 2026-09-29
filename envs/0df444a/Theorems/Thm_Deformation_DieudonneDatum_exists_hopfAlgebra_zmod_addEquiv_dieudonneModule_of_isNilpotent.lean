-- Prove2me | Theorems.Thm_Deformation_DieudonneDatum_exists_hopfAlgebra_zmod_addEquiv_dieudonneModule_of_isNilpotent
-- name    : Deformation.DieudonneDatum.exists_hopfAlgebra_zmod_addEquiv_dieudonneModule_of_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/809a873a-a82c-5fb6-a297-91da2e89bae8
-- title:
--   Finite Dieudonné datum with nilpotent V comes from a Hopf algebra
-- statement:
--   Let $p$ be a prime and let $D$ be a finite abelian group, regarded as a $\mathbb{Z}$-module, equipped with a [`Deformation.DieudonneDatum`](def/Dieudonne_DatumAndHonda.html#L14) for the element $p \in \mathbb{Z}$: that is, two $\mathbb{Z}$-linear endomorphisms $F = M.F$ and $V = M.V$ of $D$ with $F \circ V = p \cdot \mathrm{id}$ and $V \circ F = p \cdot \mathrm{id}$. Assume $V$ is nilpotent. Then there exists a type $B$ in the lowest universe, carrying a commutative ring structure, a Hopf algebra structure over $\mathbb{Z}/p$ whose comultiplication is cocommutative, and finite as a $\mathbb{Z}/p$-module, such that the Cartier dual $\mathrm{CartierDual}\,(\mathbb{Z}/p)\,B$ — the $\mathbb{Z}/p$-linear dual $\mathrm{Hom}_{\mathbb{Z}/p}(B,\mathbb{Z}/p)$ with its convolution ring structure — is a local ring, and such that there is an isomorphism of additive groups $e$ from $\mathrm{DieudonneModule}\,(\mathbb{Z}/p)\,p\,B$ onto $D$ intertwining the two operators: $e(\mathrm{frobenius}\,z) = F(e\,z)$ and $e(\mathrm{verschiebung}\,z) = V(e\,z)$ for all $z$. Here $\mathrm{DieudonneModule}\,(\mathbb{Z}/p)\,p\,B$ is the direct limit, along the Witt-vector shift maps, of the additive subgroups $\mathrm{wittHom}$ of truncated Witt vectors $x$ of length $n$ with entries in $B$ satisfying $\Delta_*x = (\iota_1)_*x + (\iota_2)_*x$ for the comultiplication $\Delta$ of $B$ and the two inclusions of $B$ into $B \otimes_{\mathbb{Z}/p} B$, with `frobenius` and `verschiebung` induced by the Frobenius and Verschiebung of truncated Witt vectors.
--
--   This is the objects (essential-surjectivity) half of Dieudonné's classification over the prime field, in the unipotent case: every finite Dieudonné module over $\mathbb{Z}_p[F,V]/(FV-p)$ with nilpotent Verschiebung is the Dieudonné module of a finite commutative unipotent group scheme over $\mathbb{F}_p$, presented in terms of a finite cocommutative Hopf algebra with local Cartier dual. It is used to build towers realising $p$-divisible data, in [`Deformation.DieudonneDatum.exists_pDivisibleTower_zmod_dieudonneModule_of_range_pow_le`](thm.html#Deformation.DieudonneDatum.exists_pDivisibleTower_zmod_dieudonneModule_of_range_pow_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_DieudonneDatum_exists_hopfAlgebra_zmod_addEquiv_dieudonneModule_of_isNilpotent.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_HopfAlgebra_CartierDual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem Deformation.DieudonneDatum.exists_hopfAlgebra_zmod_addEquiv_dieudonneModule_of_isNilpotent
    (p : ℕ) [Fact p.Prime]
    {D : Type u} [AddCommGroup D] [Finite D] (M : Deformation.DieudonneDatum (p : ℤ) D)
    (hV : IsNilpotent M.V) :
    ∃ (B : Type) (_ : CommRing B) (_ : HopfAlgebra (ZMod p) B) (_ : Coalgebra.IsCocomm (ZMod p) B)
      (_ : Module.Finite (ZMod p) B),
      IsLocalRing (CartierDual (ZMod p) B) ∧
      ∃ e : Deformation.DieudonneModule (ZMod p) p B ≃+ D,
        (∀ z, e (Deformation.DieudonneModule.frobenius (ZMod p) p B z) = M.F (e z)) ∧
        (∀ z, e (Deformation.DieudonneModule.verschiebung (ZMod p) p B z) = M.V (e z)) := by sorry
