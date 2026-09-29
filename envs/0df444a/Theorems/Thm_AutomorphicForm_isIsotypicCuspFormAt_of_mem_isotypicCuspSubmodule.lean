-- Prove2me | Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule
-- name    : AutomorphicForm.isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/8ed22074-e88b-57ca-a225-5b91151811b3
-- title:
--   Nonzero members of the isotypic cusp span are cusp forms
-- statement:
--   Let $F$ be a number field, let $D \subseteq \mathrm{GL}_2(\mathbb{A}_F)$ be a set, let $U$ assign to each ideal of $\mathcal{O}_F$ a subgroup of $\mathrm{GL}_2(\mathbb{A}_F)$, and let $\mathrm{gen}$ assign to each prime $v$ of $\mathcal{O}_F$ an element of $\mathrm{GL}_2(\mathbb{A}_F)$; these data are assembled, together with the box in $\mathbb{A}_F$ given by `adelicBox`, into the carrier data `productionPinsOf F D U gen (adelicBox F)`, whose measure-theoretic components are the Borel structures and Haar measures on $\mathrm{GL}_2(\mathbb{A}_F)$ and on $\mathbb{A}_F$, the latter conditioned on that box, and whose central subgroup is all of $\mathbb{A}_F^\times$. Let $\xi$ be a homomorphism from that central subgroup to $\mathbb{C}^\times$, let $N$ be an ideal of $\mathcal{O}_F$, let $S$ be a finite set of primes, and let $\Phi$ be a Hecke eigensystem over $\mathbb{C}$, that is, a nonzero level ideal together with families $a_v, b_v \in \mathbb{C}$ indexed by the primes. Then every $\varphi \colon \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ lying in the $\mathbb{C}$-linear span of the set of $\varphi'$ satisfying `IsIsotypicCuspFormAt F (productionPinsOf F D U gen (adelicBox F)) ξ N S Φ` and with $\varphi \neq 0$ itself satisfies that predicate: $\varphi$ satisfies `IsCuspAutomorphicFnAt` for these carrier data and $\xi$ and is `IsKfSmooth`, $\varphi$ is continuous, $\varphi(gu) = \varphi(g)$ for all $g$ and all $u$ in $U(N)$, and for every prime $v \notin S$ there is a family of $\mathrm{Nm}(v)+1$ elements forming a Hecke coset system for $U(N)$ and $\mathrm{gen}(v)$ whose associated coset sum applied to $\varphi$ equals $a_v \varphi$, while $\varphi(\mathrm{diag}(\det \mathrm{gen}(v))\, g) = (\mathrm{cNorm}\, v)^{-1} b_v\, \varphi(g)$ for all $g$.
--
--   This records that the defining conditions for an isotypic cusp form of given central character, level, exceptional set of primes and Hecke data are preserved under $\mathbb{C}$-linear combinations, so that the span of such forms consists of these forms together with $0$. It is used whenever a vector is extracted from the span — for instance a joint eigenvector of an algebra of convolution operators, or a cuspidal constituent — and must be recognised again as a genuine form with the same level and Hecke data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule.lean

import Mathlib
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm IsDedekindDomain

theorem AutomorphicForm.isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ξ : (productionPinsOf F D U gen (adelicBox F)).Z →* ℂˣ) (N : Ideal (𝓞 F))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (Φ : HeckeEigensystem F ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : φ ∈ isotypicCuspSubmodule F (productionPinsOf F D U gen (adelicBox F)) ξ N S Φ)
    (h0 : φ ≠ 0) :
    IsIsotypicCuspFormAt F (productionPinsOf F D U gen (adelicBox F)) ξ N S Φ φ := by sorry
