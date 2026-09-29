-- Prove2me | Theorems.Thm_AdjoinRoot_exists_isLocalRing_faithfullyFlat_residueField_algEquiv_of_irreducible_map
-- name    : AdjoinRoot.exists_isLocalRing_faithfullyFlat_residueField_algEquiv_of_irreducible_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/42c18051-c870-5874-9cd2-cec7a2facb95
-- title:
--   Adjoining a root with irreducible reduction over a local ring
-- statement:
--   Let $R$ be a commutative local ring (in a fixed universe) and let $f \in R[X]$ be monic; assume, as an instance hypothesis, that the reduction $\bar f = f \bmod \mathfrak m_R$, obtained by applying the residue map $R \to R/\mathfrak m_R$ coefficientwise, is irreducible in $(R/\mathfrak m_R)[X]$. The assertion is the existence of a local-ring structure on $W = R[X]/(f)$, written `AdjoinRoot f`, and of a proof that the structure map $R \to W$ is a local homomorphism (units pull back to units), such that, with respect to these, all of the following hold: $W$ is a finite $R$-module, $W$ is a free $R$-module, $W$ is faithfully flat over $R$, the ideal generated in $W$ by the image of $\mathfrak m_R$ equals the maximal ideal of $W$, and the residue field of $W$ is isomorphic, as an algebra over the residue field $R/\mathfrak m_R$, to $(R/\mathfrak m_R)[X]/(\bar f)$ (the existence of such an isomorphism being asserted as nonemptiness of the type of these algebra isomorphisms). No Noetherian, completeness, separability or domain hypothesis occurs.
--
--   This is the elementary one-step lemma for building flat local extensions of a local ring realising a prescribed algebraic extension of the residue field (as in EGA $0_{\mathrm{III}}$ 10.3.1). It is used by [`IsLocalRing.exists_isLocalRing_etale_free_residueField_algEquiv`](thm.html#IsLocalRing.exists_isLocalRing_etale_free_residueField_algEquiv) and by [`IsLocalRing.exists_isNoetherianRing_faithfullyFlat_map_maximalIdeal_eq_residueField_algEquiv_of_isAlgebraic`](thm.html#IsLocalRing.exists_isNoetherianRing_faithfullyFlat_map_maximalIdeal_eq_residueField_algEquiv_of_isAlgebraic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AdjoinRoot_exists_isLocalRing_faithfullyFlat_residueField_algEquiv_of_irreducible_map.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open Polynomial IsLocalRing in

theorem AdjoinRoot.exists_isLocalRing_faithfullyFlat_residueField_algEquiv_of_irreducible_map
    (R : Type u) [CommRing R] [IsLocalRing R]
    (f : R[X]) (hfm : f.Monic) [Fact (Irreducible (f.map (residue R)))] :
    ∃ (_ : IsLocalRing (AdjoinRoot f)) (_ : IsLocalHom (algebraMap R (AdjoinRoot f))),
      Module.Finite R (AdjoinRoot f) ∧ Module.Free R (AdjoinRoot f) ∧ Module.FaithfullyFlat R (AdjoinRoot f) ∧
      Ideal.map (algebraMap R (AdjoinRoot f)) (maximalIdeal R) = maximalIdeal (AdjoinRoot f) ∧
      Nonempty (ResidueField (AdjoinRoot f) ≃ₐ[ResidueField R] AdjoinRoot (f.map (residue R))) := by sorry
