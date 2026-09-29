-- Prove2me | Theorems.Thm_CerednikDrinfeld_Onr_isDiscreteValuationRing_equalizer_and_irreducible
-- name    : CerednikDrinfeld.Onr.isDiscreteValuationRing_equalizer_and_irreducible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/7c345f1c-247b-50a4-8f37-c4b07f1be5ad
-- title:
--   Fixed subalgebra of an automorphism is a discrete valuation ring
-- statement:
--   Let $\mathcal{O}$ be a commutative ring and $\pi \in \mathcal{O}$, and let $\mathrm{Onr}$ be a commutative ring which is a domain and an $\mathcal{O}$-algebra. Write $\varpi$ for the image of $\pi$ under the structure map $\mathcal{O} \to \mathrm{Onr}$. Assume that $\mathrm{Onr}$ is adically complete for the ideal $(\varpi)$ (in Mathlib's sense, so both Hausdorff, i.e. $\bigcap_k (\varpi)^k = 0$, and precomplete), that $(\varpi)$ is a maximal ideal of $\mathrm{Onr}$, and that $\varpi \neq 0$. Let $F$ be an $\mathcal{O}$-algebra automorphism of $\mathrm{Onr}$, and let $S$ be the equalizer subalgebra of $F$ (viewed as an $\mathcal{O}$-algebra homomorphism) and the identity, that is $S = \{x \in \mathrm{Onr} : F(x) = x\}$. The conclusion is twofold: the ring $S$ is a discrete valuation ring, and the image of $\pi$ under the structure map $\mathcal{O} \to S$ is an irreducible element of $S$, i.e. $\pi$ is a uniformiser of $S$. No hypothesis is imposed on $\mathcal{O}$ itself beyond commutativity.
--
--   This is the standing local-algebra fact about the completed maximal unramified coefficient ring $\hat{\mathcal{O}}^{\mathrm{nr}}$ used in the Cereďnik–Drinfeld setting: the ring of invariants of an $\mathcal{O}$-linear automorphism (typically a power of Frobenius) is again a complete discrete valuation ring with the same uniformiser $\pi$. It is invoked in the construction of the formal $\Omega$-side comparison, through [`CerednikDrinfeld.FormalOmega.eq_of_natural_of_forall_eq_of_comp_mk_eq_comp_val`](thm.html#CerednikDrinfeld.FormalOmega.eq_of_natural_of_forall_eq_of_comp_mk_eq_comp_val).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Onr_isDiscreteValuationRing_equalizer_and_irreducible.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.Onr.isDiscreteValuationRing_equalizer_and_irreducible
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪)
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [Algebra 𝒪 Onr]
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hπ0 : algebraMap 𝒪 Onr π ≠ 0)
    (F : Onr ≃ₐ[𝒪] Onr) :
    IsDiscreteValuationRing ↥(AlgHom.equalizer (F : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ∧ Irreducible (algebraMap 𝒪 ↥(AlgHom.equalizer (F : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) := by sorry
