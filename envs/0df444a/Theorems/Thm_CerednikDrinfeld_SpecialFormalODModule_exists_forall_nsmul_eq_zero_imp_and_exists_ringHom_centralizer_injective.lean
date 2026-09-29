-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_forall_nsmul_eq_zero_imp_and_exists_ringHom_centralizer_injective
-- name    : CerednikDrinfeld.SpecialFormalODModule.exists_forall_nsmul_eq_zero_imp_and_exists_ringHom_centralizer_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/bf62ce07-7ac8-5e82-8796-38ddcb553e17
-- title:
--   A special formal mathcal O_D-module whose endomorphism ring is an order
-- statement:
--   Let $p$ be a prime, let $k$ be a field of characteristic $p$, and let $j\colon \mathbb Z_{p^2} \to k$ be a ring homomorphism, where $\mathbb Z_{p^2}$ is realised as the Witt vectors [`CerednikDrinfeld.Zp2 p`](def/CerednikDrinfeld_SpecialFormalModule.html#L17) $= W(\mathbb F_{p^2})$. The assertion is that there exists a term $\Phi_0$ of [`CerednikDrinfeld.SpecialFormalODModule p j`](def/CerednikDrinfeld_SpecialFormalModule.html#L403), that is: a two-variable formal group law $\Phi_0.F$ over $k$, commutative, equipped with a family of endomorphisms $\mathrm{act}\,a$ indexed by $a \in \mathbb Z_{p^2}$ and a further endomorphism $\varpi$, each a law homomorphism of $\Phi_0.F$ to itself, such that $\mathrm{act}\,1$ is the identity, $\mathrm{act}(ab)$ is the composite of $\mathrm{act}\,a$ and $\mathrm{act}\,b$, $\mathrm{act}(a+b)$ is the sum of $\mathrm{act}\,a$ and $\mathrm{act}\,b$ formed via $\Phi_0.F$, $\varpi \circ \varpi = \mathrm{act}(p)$ and $\varpi \circ \mathrm{act}\,a = \mathrm{act}(\mathrm{Frob}\,a) \circ \varpi$, subject moreover to the predicate `IsSpecial` for $j$ (the submodules $\mathrm{lieZero}\,j$ and $\mathrm{lieOne}\,j$ are complementary and each is an invertible $k$-module) and to `HasHeight 4`; and such that the following two further properties hold. First, the Cartier module of $\Phi_0.F$ — pairs of power series in countably many variables with vanishing constant term, compatible with the Witt addition law and the group law — has no $p$-torsion: $p \cdot f = 0$ implies $f = 0$. Second, writing $C$ for the centraliser, inside the endomorphism ring of $\Phi_0.F$, of the set consisting of all $\mathrm{actEnd}\,a$ together with $\mathrm{varpiEnd}$, there is an injective ring homomorphism $\theta\colon C \to M_2(\mathbb Q_p)$ and a natural number $m$ with $p^m M_2(\mathbb Z_p) \subseteq \theta(C)$ (every integral matrix $M$ has $p^m M$ in the range of $\theta$) and $p^m\,\theta(C) \subseteq M_2(\mathbb Z_p)$ (for each $e \in C$, $p^m\theta(e)$ is the image of an integral matrix).
--
--   This is the existence statement for Drinfeld's standard special formal $\mathcal O_D$-module of height $4$ over a field of characteristic $p$, $\mathcal O_D$ being the maximal order of the quaternion division algebra over $\mathbb Q_p$, together with the two properties of it that are used later: $p$-torsion-freeness of its Cartier module and the fact that its ring of $\mathcal O_D$-linear endomorphisms is an order in $M_2(\mathbb Q_p)$. It feeds the corresponding statement over algebraically closed fields, [`CerednikDrinfeld.SpecialFormalODModule.exists_ringHom_centralizer_injective_of_isAlgClosed`](thm.html#CerednikDrinfeld.SpecialFormalODModule.exists_ringHom_centralizer_injective_of_isAlgClosed), in the Čerednik–Drinfeld uniformisation input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormalODModule_exists_forall_nsmul_eq_zero_imp_and_exists_ringHom_centralizer_injective.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.SpecialFormalODModule.exists_forall_nsmul_eq_zero_imp_and_exists_ringHom_centralizer_injective
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    (j : CerednikDrinfeld.Zp2 p →+* k) :
    ∃ Φ₀ : CerednikDrinfeld.SpecialFormalODModule p j,
      (∀ f : MvFormalGroup.CartierModule p Φ₀.F, p • f = 0 → f = 0) ∧
      ∃ θ : Subring.centralizer
            (Set.range Φ₀.toFormalODModule.actEnd ∪ {Φ₀.toFormalODModule.varpiEnd}) →+*
          Matrix (Fin 2) (Fin 2) ℚ_[p],
        Function.Injective θ ∧
        ∃ m : ℕ,
          (∀ M : Matrix (Fin 2) (Fin 2) ℤ_[p],
            ∃ e, θ e = (p : ℚ_[p]) ^ m • M.map ((↑) : ℤ_[p] → ℚ_[p])) ∧
          (∀ e, ∃ M : Matrix (Fin 2) (Fin 2) ℤ_[p],
            (p : ℚ_[p]) ^ m • θ e = M.map ((↑) : ℤ_[p] → ℚ_[p])) := by sorry
