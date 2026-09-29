-- Prove2me | Theorems.Thm_CohCarrier_HeckeData_exists_eigenvector_H1_of_toML_ne_zero
-- name    : CohCarrier.HeckeData.exists_eigenvector_H1_of_toML_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/6c841a0f-3569-534e-a0a2-d436fc345002
-- title:
--   Deligne–Serre lifting for transfer Hecke operators on H¹(Γ_H(M))
-- statement:
--   Let $\mathcal O$ be a complete discrete valuation ring (a domain, adically complete for its maximal ideal) of characteristic zero with finite residue field, let $M \ge 1$ and let $H \le (\mathbb Z/M)^\times$; write $V =$ [`CohCarrier.H1 M H 𝒪`](def/CohCarrier_Level.html#L162) for the group of additive maps from $\Gamma_H(M)$, viewed additively, to $\mathcal O$. Let $D$ be a `HeckeData` over $\mathcal O$ on $V$ with values in the residue field of $\mathcal O$, that is: a type `D.Gen` of generators, pairwise commuting $\mathcal O$-endomorphisms `D.op g` of $V$, and residual scalars `D.θbar g` in the residue field. Assume given primes $\ell(g)$ with `D.op g` equal to the transfer Hecke operator [`CohCarrier.heckeT M H (ℓ g) 𝒪`](def/CohCarrier_Level.html#L250) for every $g$. Let $W \subseteq V$ be an $\mathcal O$-submodule stable under every `D.op g`, and let $\varphi \in W$ have non-zero image under `D.toML`, the canonical map of $V$ into its localisation at the prime complement of `D.mTheta`, the kernel of `D.thetaTilde` on the free algebra `MvPolynomial D.Gen 𝒪`. Then there exist a complete discrete valuation ring $\mathcal O'$ of characteristic zero with finite residue field, module-finite over $\mathcal O$ along an injective local algebra map; an algebraically closed field $F$ with injective structure map $\mathcal O' \to F$; elements $\lambda_g \in \mathcal O'$ whose residues are the images of the `D.θbar g` under the induced map of residue fields; and a non-zero $c \in$ [`CohCarrier.H1 M H F`](def/CohCarrier_Level.html#L162) lying in the $F$-span of the image of $W$ under coefficient extension $\mathcal O \to \mathcal O' \to F$, with [`CohCarrier.heckeT M H (ℓ g) F c`](def/CohCarrier_Level.html#L250) $= \lambda_g \, c$ for all $g$.
--
--   This is the Deligne–Serre lifting lemma in adic form, specialised to the transfer Hecke operators acting on the first cohomology of $\Gamma_H(M)$ with trivial coefficients: a residual eigensystem realised by a class in a Hecke-stable sublattice is lifted to a genuine common eigenvector over a finite extension of the coefficient ring. It is used in the identification of residues of Hecke eigenvalues with traces of Frobenius and in the integral Hecke congruence statements that feed the level-lowering argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_HeckeData_exists_eigenvector_H1_of_toML_ne_zero.lean

import Definitions.Def_CohCarrier_Inst
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem CohCarrier.HeckeData.exists_eigenvector_H1_of_toML_ne_zero
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (D : CohCarrier.HeckeData 𝒪 (CohCarrier.H1 M H 𝒪) (ResidueField 𝒪))

    (ℓ : D.Gen → ℕ) (hℓ : ∀ g : D.Gen, (ℓ g).Prime)
    (hop : ∀ (g : D.Gen) (ψ : CohCarrier.H1 M H 𝒪),
      D.op g ψ = (haveI : NeZero (ℓ g) := ⟨(hℓ g).ne_zero⟩; CohCarrier.heckeT M H (ℓ g) 𝒪 ψ))

    (W : Submodule 𝒪 (CohCarrier.H1 M H 𝒪)) (hW : ∀ (g : D.Gen), ∀ w ∈ W, D.op g w ∈ W)
    (φ : CohCarrier.H1 M H 𝒪) (hφW : φ ∈ W) (hφ : D.toML φ ≠ 0) :
    ∃ (𝒪' : Type) (_ : CommRing 𝒪') (_ : IsDomain 𝒪') (_ : IsDiscreteValuationRing 𝒪')
      (_ : IsAdicComplete (maximalIdeal 𝒪') 𝒪') (_ : Finite (ResidueField 𝒪'))
      (_ : CharZero 𝒪') (_ : Algebra 𝒪 𝒪') (_ : Module.Finite 𝒪 𝒪')
      (_ : IsLocalHom (algebraMap 𝒪 𝒪')),
    Function.Injective (algebraMap 𝒪 𝒪') ∧
    ∃ (F : Type) (_ : Field F) (_ : IsAlgClosed F) (_ : Algebra 𝒪' F),
    Function.Injective (algebraMap 𝒪' F) ∧
    ∃ lam : D.Gen → 𝒪',
      (∀ g : D.Gen, residue 𝒪' (lam g) = ResidueField.map (algebraMap 𝒪 𝒪') (D.θbar g)) ∧
      ∃ c : CohCarrier.H1 M H F, c ≠ 0 ∧
        c ∈ Submodule.span F
          ((fun w : CohCarrier.H1 M H 𝒪 =>
              ((algebraMap 𝒪' F).comp (algebraMap 𝒪 𝒪')).toAddMonoidHom.comp w) '' (W : Set _)) ∧
        ∀ g : D.Gen,
          (haveI : NeZero (ℓ g) := ⟨(hℓ g).ne_zero⟩; CohCarrier.heckeT M H (ℓ g) F c) =
            algebraMap 𝒪' F (lam g) • c := by sorry
