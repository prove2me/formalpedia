-- Prove2me | Theorems.Thm_Deformation_DieudonneModule_eval_injective_and_exists_eval_eq_of_isLocalRing_cartierDual
-- name    : Deformation.DieudonneModule.eval_injective_and_exists_eval_eq_of_isLocalRing_cartierDual
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/27d32056-e202-5df6-9e8f-a44a8649a10f
-- title:
--   Points of a unipotent group scheme as F,V-maps of Dieudonné modules
-- statement:
--   Let $p$ be a prime, and let $B$ be a commutative ring carrying a Hopf algebra structure over $\mathbf F_p =$ `ZMod p` whose comultiplication is cocommutative and which is finite as a $\mathbf F_p$-module; assume the Cartier dual $\mathrm{CartierDual}(\mathbf F_p,B)$, namely the $\mathbf F_p$-linear dual $B^{\vee}$ with its convolution ring structure, is a local ring. Let $S$ be any commutative $\mathbf F_p$-algebra. Here $\mathrm{DieudonneModule}(\mathbf F_p,p,B)$ is the direct limit over $n$ of the additive subgroups $\mathrm{wittHom}$ of $W_n(B)$ cut out by the primitivity condition $W_n(\Delta)(x) = W_n(\iota_1)(x) + W_n(\iota_2)(x)$ in $W_n(B\otimes_{\mathbf F_p}B)$, the transition maps being induced by iterated Verschiebung on truncated Witt vectors, and $\mathrm{UnipotentWittCovector}(p,S)$ is the direct limit of the $W_n(S)$ along the same shift maps; both carry additive endomorphisms $F$ and $V$ induced levelwise. For an $\mathbf F_p$-algebra map $f : B \to S$, $\mathrm{eval}$ is the additive map obtained by including primitive vectors into $W_n(B)$ and applying $W_n(f)$. The assertion is twofold: $f \mapsto \mathrm{eval}(f)$ is injective on $\mathbf F_p$-algebra maps $B \to S$; and every additive $\varphi$ from the Dieudonné module to the unipotent Witt covectors commuting with $F$ and with $V$ equals $\mathrm{eval}(f)$ for some such $f$.
--
--   This is the statement that, for a finite commutative unipotent group scheme $G = \operatorname{Spec} B$ over the prime field, the comparison map $G(S) \to \operatorname{Hom}_{F,V}(M(G), CW^u(S))$ of contravariant Dieudonné theory is bijective for every $\mathbf F_p$-algebra $S$ (Demazure–Gabriel, Chap. V, §1, no. 4). It is used in the analysis of the cotangent space of such a group scheme and in the description of Honda systems and the Fontaine functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_DieudonneModule_eval_injective_and_exists_eval_eq_of_isLocalRing_cartierDual.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_Dieudonne_UnipotentWittCovector
import Definitions.Def_HopfAlgebra_CartierDual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem Deformation.DieudonneModule.eval_injective_and_exists_eval_eq_of_isLocalRing_cartierDual
    (p : ℕ) [Fact p.Prime]
    (B : Type u) [CommRing B] [HopfAlgebra (ZMod p) B] [Coalgebra.IsCocomm (ZMod p) B]
    [Module.Finite (ZMod p) B] (hB : IsLocalRing (CartierDual (ZMod p) B))
    (S : Type v) [CommRing S] [Algebra (ZMod p) S] :
    (∀ f g : B →ₐ[ZMod p] S,
        Deformation.DieudonneModule.eval (ZMod p) p f = Deformation.DieudonneModule.eval (ZMod p) p g →
        f = g) ∧
    (∀ φ : Deformation.DieudonneModule (ZMod p) p B →+ Deformation.UnipotentWittCovector p S,
        (∀ z, φ (Deformation.DieudonneModule.frobenius (ZMod p) p B z) =
          Deformation.UnipotentWittCovector.frobenius (ZMod p) p S (φ z)) →
        (∀ z, φ (Deformation.DieudonneModule.verschiebung (ZMod p) p B z) =
          Deformation.UnipotentWittCovector.verschiebung p S (φ z)) →
        ∃ f : B →ₐ[ZMod p] S, Deformation.DieudonneModule.eval (ZMod p) p f = φ) := by sorry
