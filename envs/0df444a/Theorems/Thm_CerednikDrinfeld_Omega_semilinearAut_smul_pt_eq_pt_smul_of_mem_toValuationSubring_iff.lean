-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_semilinearAut_smul_pt_eq_pt_smul_of_mem_toValuationSubring_iff
-- name    : CerednikDrinfeld.Omega.semilinearAut_smul_pt_eq_pt_smul_of_mem_toValuationSubring_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/a2e6f9ea-cf70-5589-9df7-12554e5827d3
-- title:
--   Semilinear automorphism realised by (n,t) transports places accordingly
-- statement:
--   Fix a valuation subring $A$ of $\overline{\mathbb{Q}}$ and write $C$ for the completion $A.\mathrm{valuation}.\mathrm{Completion}$. Let $K_0$ be a field with an algebra map to $C$ (with decidable equality on $C$), and let $\varpi$ be a pseudo-uniformizer: an element of $K_0$ whose image in $C$ has valuation strictly between $0$ and $1$ and such that every nonzero element of $K_0$ has valuation squeezed between $|\varpi|^N$ and $|\varpi|^{-N}$ for some $N$. Let $G$ be a group, $\rho : G \to \mathrm{PGL}(2,K_0)$, and assume `Omega.HolRingOf ϖ ρ` — the ring `holRing ϖ` of functions on the Drinfeld upper half plane $\Omega = C \setminus \mathrm{im}(K_0 \to C)$ that on each affinoid are bounded uniform limits of pole-free rational functions — is a domain. Let $\Gamma \le G$, let $FC$ be a field over $C$, and let $eFC$ be a $C$-algebra isomorphism of $FC$ with the subfield of $\Gamma$-invariants in $\mathrm{Frac}(\mathrm{HolRingOf}\,\varpi\,\rho)$. Let $pt$ assign to each $z \in \Omega$ a place of $FC$ over $C$ (a proper valuation subring containing the image of $C$ and being a principal ideal ring), subject to the dictionary hypothesis: $x$ lies in the valuation ring of $pt(z)$ exactly when $eFC(x)$, viewed in the fraction field, is a fraction $g/h$ with $g,h$ holomorphic, $h$ a non-zero-divisor and $h(z) \ne 0$. Let $g$ be a semilinear automorphism, i.e. a pair consisting of a ring automorphism of $FC$ and one of $C$ compatible with the structure map, let $n \in G$, and let $t$ be a ring automorphism of $C$ preserving the valuation and fixing $K_0$ pointwise. Assume $g$ is realised by $(n,t)$: for every $y \in FC$, the image of $eFC(g \cdot y)$ in $\mathrm{Frac}(\mathrm{HolRingOf}\,\varpi\,\rho)$ equals $n$ acting on the image of $eFC(y)$ under the automorphism of the fraction field induced by $t$ (acting on $C$ by $t$ and on holomorphic functions coefficientwise). Then for every $z \in \Omega$ one has $g \cdot pt(z) = pt(\rho(n) \cdot t(z))$, where $g$ acts on places through the induced action on valuation subrings and $\rho(n)$ acts on $\Omega$ by Möbius transformations.
--
--   This is the equivariance half of the point-to-place dictionary for Mumford quotients of the Drinfeld upper half plane: a symmetry of the quotient field that is realised analytically by a group element $n$ together with an isometric coefficient automorphism $t$ moves the place attached to $z$ to the place attached to $\rho(n)\,t(z)$. It feeds into the construction of equivariant period data for the degree-zero Picard group of a Mumford quotient, in [`AlgebraicCurve.Pic0.periodDatum_equivariant_of_theta_pinned_uniformization_of_mumfordQuotient`](thm.html#AlgebraicCurve.Pic0.periodDatum_equivariant_of_theta_pinned_uniformization_of_mumfordQuotient).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_semilinearAut_smul_pt_eq_pt_smul_of_mem_toValuationSubring_iff.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_MumfordQuotientNormalizer
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ValuationSubring_CompletionDecompositionAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve

theorem CerednikDrinfeld.Omega.semilinearAut_smul_pt_eq_pt_smul_of_mem_toValuationSubring_iff
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (K₀ : Type) [Field K₀] [Algebra K₀ A.valuation.Completion] [DecidableEq A.valuation.Completion]
    (ϖ : Omega.PseudoUniformizer K₀ A.valuation.Completion)
    (G : Type) [Group G] (ρ : G →* PGL(2, K₀))
    [IsDomain (Omega.HolRingOf ϖ ρ)]
    (Γ : Subgroup G)
    (FC : Type) [Field FC] [Algebra A.valuation.Completion FC]
    (eFC : FC ≃ₐ[A.valuation.Completion] ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ))
    (pt : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → Place A.valuation.Completion FC)
    (hpt_mem : ∀ (z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (x : FC),
        x ∈ (pt z).toValuationSubring ↔
          ∃ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
            (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ≠ 0 ∧ ((eFC x : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk g ⟨h, hh⟩)
    (g : SemilinearAut A.valuation.Completion FC) (n : G) (t : Omega.IsometricAut K₀ A.valuation.Completion)
    (hreal : ∀ y : FC, ((eFC (g • y) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ t) ((eFC y : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ))) :
    ∀ z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion),
      g • pt z = pt ((ρ n) • ⟨t.toRingEquiv (z : A.valuation.Completion), t.mapsTo_upperHalfPlane z.2⟩) := by sorry
