-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_nonempty_and_exists_isIsogenyOfHeight_and_exists_ringHom_centralizer_of_isAlgClosed
-- name    : CerednikDrinfeld.SpecialFormalODModule.nonempty_and_exists_isIsogenyOfHeight_and_exists_ringHom_centralizer_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/29e5ecf6-d501-5eca-b0aa-c6449d859e3f
-- title:
--   Special formal mathcal O_D-modules: existence, isogeny, endomorphism order
-- statement:
--   Let $p$ be a prime and let $k$ be an algebraically closed field of characteristic $p$, made into an algebra over $\mathbb Z_{p^2} = W(\mathbb F_{p^2})$ (the project's `Zp2 p`) by a ring homomorphism $j$. Here a `SpecialFormalODModule` for $j$ consists of a commutative $2$-dimensional formal group law $F$ over $k$ together with a family `act` of law endomorphisms of $F$ indexed by $\mathbb Z_{p^2}$ and a further law endomorphism `varpi`, such that `act` sends $1$ to the identity series, turns products into composition of series and sums into addition via $F$, `varpi` composed with itself equals `act` at $p$, and `varpi` composed with `act a` equals `act` of the Witt-vector Frobenius of $a$ composed with `varpi`; in addition the predicates `IsSpecial` for $j$ and `HasHeight 4` are required of the underlying $\mathcal O_D$-module. Three assertions are made. First, such an object exists. Second, for any two such $\Phi,\Phi'$ there are a pair of two-variable power series $\rho$ over $k$ and an $h \in \mathbb N$ with `IsIsogenyOfHeight` for $\Phi,\Phi',\rho,h$, i.e. $\rho$ satisfies `IsODHom` from $\Phi$ to $\Phi'$ and `HasKernelOfDegree` $p^h$. Third, for each $\Phi$ there is an injective ring homomorphism $\theta$ from the centraliser, inside the endomorphism ring of $F$, of the set consisting of all `actEnd` of $\Phi$ together with `varpiEnd` of $\Phi$, into $M_2(\mathbb Q_p)$, and an $m \in \mathbb N$ such that every $M \in M_2(\mathbb Z_p)$ has $p^m M$ in the image of $\theta$, while $p^m \theta(e)$ has entries in $\mathbb Z_p$ for every $e$; that is, $p^m M_2(\mathbb Z_p) \subseteq \theta(\mathrm{End}) \subseteq p^{-m} M_2(\mathbb Z_p)$.
--
--   This is Drinfeld's basic structure result on special formal $\mathcal O_D$-modules of height $4$ over an algebraically closed field of characteristic $p$: they exist, are unique up to isogeny, and their ring of $\mathcal O_D$-linear endomorphisms is an order in $M_2(\mathbb Q_p)$, whence the group of self-quasi-isogenies is $GL_2(\mathbb Q_p)$. It is the input used to fix the base point of Drinfeld's moduli problem of rigidified special formal $\mathcal O_D$-modules in the Čerednik–Drinfeld uniformisation, and it is cited in the package `exists_isCritical_and_exists_basis_injective_endMatrixQ_and_exists_pow_smul_of_isAlgClosed`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormalODModule_nonempty_and_exists_isIsogenyOfHeight_and_exists_ringHom_centralizer_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.SpecialFormalODModule.nonempty_and_exists_isIsogenyOfHeight_and_exists_ringHom_centralizer_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    (j : CerednikDrinfeld.Zp2 p →+* k) :
    Nonempty (CerednikDrinfeld.SpecialFormalODModule p j) ∧
    (∀ Φ Φ' : CerednikDrinfeld.SpecialFormalODModule p j,
      ∃ (ρ : CerednikDrinfeld.SpecialFormal.Series k) (h : ℕ),
        CerednikDrinfeld.FormalODModule.IsIsogenyOfHeight Φ.toFormalODModule Φ'.toFormalODModule ρ h) ∧
    (∀ Φ : CerednikDrinfeld.SpecialFormalODModule p j,
      ∃ θ : Subring.centralizer
            (Set.range Φ.toFormalODModule.actEnd ∪ {Φ.toFormalODModule.varpiEnd}) →+*
          Matrix (Fin 2) (Fin 2) ℚ_[p],
        Function.Injective θ ∧
        ∃ m : ℕ,
          (∀ M : Matrix (Fin 2) (Fin 2) ℤ_[p],
            ∃ e, θ e = (p : ℚ_[p]) ^ m • M.map ((↑) : ℤ_[p] → ℚ_[p])) ∧
          (∀ e, ∃ M : Matrix (Fin 2) (Fin 2) ℤ_[p],
            (p : ℚ_[p]) ^ m • θ e = M.map ((↑) : ℤ_[p] → ℚ_[p]))) := by sorry
