-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_fracAct_prod_fracAct_eq_transfer_inv_mul
-- name    : CerednikDrinfeld.Omega.fracAct_prod_fracAct_eq_transfer_inv_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/95cc5bc4-fe76-55af-8e3d-35df5e998834
-- title:
--   Coset norm of a χ-automorphic function has multiplier Ver(χ)
-- statement:
--   Let $K_0$ be a field and $K$ a $K_0$-algebra which is a field, carrying a valuation with values in a linearly ordered commutative group with zero $\Gamma_0$, and let $\varpi$ be a pseudo-uniformiser, i.e. an element $\varpi \in K_0$ with $0 < v(\varpi) < 1$ in $K$ such that every nonzero $a \in K_0$ satisfies $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$ for some $N$. Write $\mathrm{holRing}\ \varpi$ for the subring of functions on the Drinfeld upper half plane $K \setminus \mathrm{im}(K_0 \to K)$ that are holomorphic, in the sense of uniform approximation by uniformly bounded pole-free rational functions, on each affinoid $\mathrm{affinoid}\ \varpi\ n$; it is assumed to be a domain, and $\mathrm{merField}\ \varpi$ denotes its fraction field. For $g \in \mathrm{PGL}(2,K_0)$, $\mathrm{fracAct}$ extends the action of $g$ on $\mathrm{holRing}\ \varpi$ to a ring automorphism of $\mathrm{merField}\ \varpi$. Given a group $G$ with a homomorphism $\rho : G \to \mathrm{PGL}(2,K_0)$, a finite-index subgroup $\Gamma' \le G$ with finite quotient $G/\Gamma'$, a set-theoretic section $s : G/\Gamma' \to G$ of the quotient map, an element $f \in \mathrm{merField}\ \varpi$ and a homomorphism $\chi : \Gamma' \to K^\times$ such that $\rho(\gamma)$ acts on $f$ as multiplication by the image of $\chi(\gamma)^{-1}$ for all $\gamma \in \Gamma'$, the conclusion is that for every $\gamma \in G$ the element $Nf := \prod_{q \in G/\Gamma'} \mathrm{fracAct}(\rho(s\,q))\,f$ satisfies $\mathrm{fracAct}(\rho(\gamma))\,Nf = (\mathrm{MonoidHom.transfer}\ \chi\ \gamma)^{-1} \cdot Nf$, the scalar being taken in $K^\times$ and mapped into $\mathrm{merField}\ \varpi$.
--
--   This is the statement that the norm of a $\chi$-automorphic meromorphic function on the Drinfeld upper half plane over the cosets of a finite-index subgroup is automorphic for the whole group, with multiplier the transfer (Verlagerung) of $\chi$. It serves the construction of theta functions and equivariant uniformisations for Mumford quotients, and is used in the identification of multipliers with transfers and in the construction of natural families of equivariant uniformisations of degree-zero Picard groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_fracAct_prod_fracAct_eq_transfer_inv_mul.lean

import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Mathlib.GroupTheory.Transfer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Omega.fracAct_prod_fracAct_eq_transfer_inv_mul
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ : PseudoUniformizer K₀ K) [IsDomain ↥(holRing ϖ)]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀))
    (Γ' : Subgroup G) [Γ'.FiniteIndex] [Fintype (G ⧸ Γ')] (s : G ⧸ Γ' → G) (hs : ∀ q : G ⧸ Γ', (QuotientGroup.mk (s q) : G ⧸ Γ') = q)
    (f : merField ϖ) (χ : ↥Γ' →* Kˣ)
    (hf : ∀ γ : ↥Γ', Mumford.fracAct PGL(2, K₀) ↥(holRing ϖ) (ρ γ) f =
      algebraMap K (merField ϖ) (((χ γ)⁻¹ : Kˣ) : K) * f) :
    ∀ γ : G, Mumford.fracAct PGL(2, K₀) ↥(holRing ϖ) (ρ γ)
        (∏ q : G ⧸ Γ', Mumford.fracAct PGL(2, K₀) ↥(holRing ϖ) (ρ (s q)) f) =
      algebraMap K (merField ϖ) (((MonoidHom.transfer χ γ)⁻¹ : Kˣ) : K) *
        ∏ q : G ⧸ Γ', Mumford.fracAct PGL(2, K₀) ↥(holRing ϖ) (ρ (s q)) f := by sorry
