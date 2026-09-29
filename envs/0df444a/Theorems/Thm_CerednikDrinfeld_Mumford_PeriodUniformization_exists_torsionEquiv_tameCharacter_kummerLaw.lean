-- Prove2me | Theorems.Thm_CerednikDrinfeld_Mumford_PeriodUniformization_exists_torsionEquiv_tameCharacter_kummerLaw
-- name    : CerednikDrinfeld.Mumford.PeriodUniformization.exists_torsionEquiv_tameCharacter_kummerLaw
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/ebcf2cf4-d7f4-5952-80a2-75f50b33ea14
-- title:
--   p-torsion character and tame Kummer law for a Mumford period uniformisation
-- statement:
--   Fix primes $p \neq r$, finite types $E$ and $V$, a degeneracy datum $D$ on $(E,V)$ (maps $a,b : E \to V$ and widths $w : E \to \mathbb{N}^{+}$), Hecke data $H$ for $D$, a valuation subring $A$ of an algebraic closure of $\mathbb{Q}$ with $r$ a nonunit of $A$, an additive group $T$ carrying a ring homomorphism $\mathrm{hecke}$ from $\mathrm{HeckeAlg} = \mathbb{Z}[X_\ell : \ell \text{ prime}]$ to $\operatorname{End}_{\mathbb{Z}} T$ and a homomorphism $\mathrm{gal}$ from $\operatorname{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ to the additive automorphisms of $T$, and a period uniformisation $\mathcal{U}$ of these data at $A$: a period field $K$ inside the completion of $A$'s valuation, an order map, a symmetric pairing $Q$ on the ribbon kernel $Z = \ker(\text{pushforward along } a) \cap \ker(\text{pushforward along } b) \subseteq (E \to \mathbb{Z})$ with $\operatorname{ord} \circ Q$ the width Gram form $\mathrm{ribbonGram}\,D$, a module $\mathcal{U}.P.U$ of torus points $\operatorname{Hom}_{\mathbb{Z}}(Z, \text{(completion)}^{\times})$, the period map $\mathcal{U}.P.QL$, and $\mathcal{U}.e : \mathcal{U}.P.U \to T$. Let $\zeta$ be a primitive $p$-th root of unity in the completion. Then there is an additive isomorphism $\chi$ from the $p$-torsion of $\mathcal{U}.P.U$ onto $\operatorname{Hom}_{\mathbb{Z}}(Z, \mathbb{Z}/p)$ with $v(z) = \zeta^{\chi(v)(z)}$ for all such $v$ and all $z \in Z$, and a surjective homomorphism $\mathrm{tame}$ from the inertia subgroup $A.\mathrm{inertiaSubgroupIn}\,\mathbb{Q}$ (the image in $\operatorname{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ of the inertia subgroup of the decomposition subgroup) to $\mathbb{Z}/p$, written multiplicatively, such that whenever $\sigma$ lies in that inertia subgroup, $u \in \mathcal{U}.P.U$ and $x \in Z$ satisfy $p \cdot u = \mathcal{U}.P.QL\,x$, there exists a $p$-torsion element $v$ with $\mathrm{gal}(\sigma)(\mathcal{U}.e\,u) = \mathcal{U}.e\,u + \mathcal{U}.e\,v$ and $\chi(v) = \mathrm{tame}(\sigma) \cdot (\mathrm{ribbonGram}\,D\,x \bmod p)$.
--
--   This is the inertia-theoretic content of the passage from a Mumford-style period uniformisation to a purely toric one: the $p$-torsion dictionary $U[p] \cong \operatorname{Hom}(Z,\mathbb{Z}/p)$, the surjective tame character on inertia at $A$, and the Kummer law describing the Galois action on $p$-division points of the uniformised group in terms of the monodromy pairing modulo $p$. It supplies the `torsionEquiv`, `tame`, `tame_surjective` and `kummer` data used by [`CerednikDrinfeld.Mumford.nonempty_toricUniformization_of_periodUniformization`](thm.html#CerednikDrinfeld.Mumford.nonempty_toricUniformization_of_periodUniformization).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Mumford_PeriodUniformization_exists_torsionEquiv_tameCharacter_kummerLaw.lean

import Definitions.Def_CerednikDrinfeld_MumfordUniformization
import Definitions.Def_CerednikDrinfeld_ToricUniformization
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford ModularCurve

theorem CerednikDrinfeld.Mumford.PeriodUniformization.exists_torsionEquiv_tameCharacter_kummerLaw
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime] (hpr : p ≠ r)
    {E V : Type} [Fintype E] [Fintype V] [DecidableEq V]
    {D : DegeneracyData E V} {H : HeckeData D}
    {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime r}
    {T : Type} [AddCommGroup T] {hecke : HeckeAlg →+* Module.End ℤ T}
    {gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* AddAut T}
    (𝒰 : PeriodUniformization r D H A hA T hecke gal)
    (ζ : (A.valuation.Completion)ˣ) (hζ : IsPrimitiveRoot ζ p) :
    ∃ χ : ↥(Submodule.torsionBy ℤ ↥𝒰.P.U (p : ℤ)) ≃+ (↥(ribbonKernel D) →ₗ[ℤ] ZMod p),
      (∀ (v : ↥(Submodule.torsionBy ℤ ↥𝒰.P.U (p : ℤ))) (z : ↥(ribbonKernel D)),
        Additive.toMul ((((v : ↥𝒰.P.U) : 𝒰.P.TorusPoints) z)) = ζ ^ (χ v z).val) ∧
      ∃ tame : ↥(A.inertiaSubgroupIn ℚ) →* Multiplicative (ZMod p), Function.Surjective tame ∧
        ∀ (σ : ↥(A.inertiaSubgroupIn ℚ)) (u : ↥𝒰.P.U) (x : ↥(ribbonKernel D)),
          (p : ℤ) • (u : 𝒰.P.TorusPoints) = 𝒰.P.QL x →
            ∃ v : ↥(Submodule.torsionBy ℤ ↥𝒰.P.U (p : ℤ)),
              gal (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (𝒰.e u) = 𝒰.e u + 𝒰.e (v : ↥𝒰.P.U) ∧
                χ v = (Multiplicative.toAdd (tame σ)) • ribbonGramModP p D x := by sorry
