-- Prove2me | Theorems.Thm_AutomorphicForm_IsIsotypicCuspFormAt_of_le_of_subset
-- name    : AutomorphicForm.IsIsotypicCuspFormAt.of_le_of_subset
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/82e887e1-2f51-5ae2-8310-e682ffb29ca6
-- title:
--   Monotonicity of isotypic cusp forms in level and bad set
-- statement:
--   Let $F$ be a number field and $D$ an arbitrary subset of $\mathrm{GL}_2(\mathbb{A}_F)$. Work with the carrier data $\mathrm{productionPinsOf}$ attached to $F$, $D$, the assignment $N \mapsto \mathrm{levelOne}(N) \sqcap \ker(\mathrm{glArch})$, the local generators $v \mapsto \mathrm{heckeGen}(v)$ and the box $\mathrm{adelicBox}(F)$; these fix the Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$, the window $D$, the full group $\top$ of idele units as central subgroup, and the additive adelic Haar measure conditioned on the box. Let $\xi$ be a homomorphism from that central subgroup to $\mathbb{C}^\times$, let $N' \le N$ be ideals of $\mathcal{O}_F$ with $N' \ne \bot$, let $S \subseteq S'$ be finite sets of finite places such that no $v \notin S'$ divides $N'$, and let $\Psi$ be a Hecke eigensystem over $\mathbb{C}$ (a nonzero level together with families $a, b$ indexed by the finite places). Assume $\varphi : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ satisfies $\mathrm{IsIsotypicCuspFormAt}$ for the datum $(\xi, N, S, \Psi)$: it is a $K_f$-smooth cuspidal automorphic function for $\xi$, continuous, right invariant under $\mathrm{levelOne}(N) \sqcap \ker(\mathrm{glArch})$, for each $v \notin S$ an eigenfunction with eigenvalue $\Psi.a\,v$ of the Hecke coset sum for that level group and the generator $\mathrm{heckeGen}(v)$ (for some system of $\mathrm{absNorm}(v)+1$ coset representatives), and for each $v \notin S$ satisfies $\varphi(\mathrm{centralScalar}(\det \mathrm{heckeGen}(v)) \cdot g) = (\mathrm{cNorm}\,v)^{-1}\,\Psi.b\,v \cdot \varphi(g)$ for all $g$. Then $\varphi$ satisfies the same predicate for the datum $(\xi, N', S', \Psi)$.
--
--   This is the standard compatibility of an automorphic eigenform with passage to a deeper level and a larger set of excluded places: away from the primes of the new level the unramified Hecke eigenvalues and the central character values are unchanged. It is used to put several eigenforms at a common level before comparing them, and is cited in the construction of irreducible automorphic representations and in the archimedean Casimir statements of this development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_IsIsotypicCuspFormAt_of_le_of_subset.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm

theorem AutomorphicForm.IsIsotypicCuspFormAt.of_le_of_subset
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))
    (ξ : (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
    {N N' : Ideal (𝓞 F)} (hN : N' ≤ N) (hN'0 : N' ≠ ⊥)
    {S S' : Finset (HeightOneSpectrum (𝓞 F))} (hSS' : S ⊆ S')
    (hS' : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S' → ¬ v.asIdeal ∣ N')
    (Ψ : HeckeEigensystem F ℂ) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsIsotypicCuspFormAt F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ φ) :
    IsIsotypicCuspFormAt F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N' S' Ψ φ := by sorry
