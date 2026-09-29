-- Prove2me | Theorems.Thm_AutomorphicForm_isotypicCuspSubmodule_principal_bot_eq_bot_of_productionPinsOf
-- name    : AutomorphicForm.isotypicCuspSubmodule_principal_bot_eq_bot_of_productionPinsOf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/b5294afa-3f9e-5001-8bef-0858905cd536
-- title:
--   Isotypic cusp forms of zero principal level vanish
-- statement:
--   Let $F$ be a number field, with ring of integers $\mathcal{O}_F$ and adele ring $\mathbb{A}_F$, let $D$ be a subset of $\mathrm{GL}_2(\mathbb{A}_F)$ and $B$ a subset of $\mathbb{A}_F$. Let `pins` denote the carrier datum `productionPinsOf` attached to $F$, $D$, $B$ and the two assignments $N \mapsto$ `principalLevel` $(\mathcal{O}_F,F,N) \sqcap$ `finiteAdelicGL2Subgroup` $F$ (the principal level subgroup $\mathrm{levelOne}(N)$ intersected with its conjugate by the Weyl element, intersected with the kernel of the archimedean projection `glArch`) and $v \mapsto$ `heckeGen` $(\mathcal{O}_F,F,v)$; its remaining components are the Borel $\sigma$-algebra and Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$, the full central subgroup $Z = \top \le \mathbb{A}_F^\times$, the Borel $\sigma$-algebra on $\mathbb{A}_F$, and the additive Haar measure of $\mathbb{A}_F$ conditioned on $B$. Let $\xi \colon \mathbb{A}_F^\times \to \mathbb{C}^\times$ be a homomorphism, $S$ a finite set of finite places of $F$, and $\Psi$ a Hecke eigensystem over $\mathbb{C}$ for $F$ (a nonzero level ideal together with families $a_v, b_v \in \mathbb{C}$). Then the $\mathbb{C}$-submodule of functions $\mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ spanned by the isotypic cusp forms `IsIsotypicCuspFormAt` for these data at level the zero ideal $\bot$ is the zero submodule; equivalently, no nonzero function satisfies the defining conditions at level $\bot$.
--
--   A degeneracy statement about the level conventions: with the zero ideal as level the prescribed right-invariance subgroup is too small for the Hecke coset conditions to be satisfiable, so the isotypic cuspidal space is zero. It serves as the boundary case in [`AutomorphicForm.eq_of_isCuspConstituent_of_cuspConstituentMeets_principal_of_coversModCentre`](thm.html#AutomorphicForm.eq_of_isCuspConstituent_of_cuspConstituentMeets_principal_of_coversModCentre), allowing the nonzero-level hypothesis to be dispensed with there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isotypicCuspSubmodule_principal_bot_eq_bot_of_productionPinsOf.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm

theorem AutomorphicForm.isotypicCuspSubmodule_principal_bot_eq_bot_of_productionPinsOf
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F)) (B : Set (AdeleRing (𝓞 F) F))
    (ξ : (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) B).Z →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ) :
    isotypicCuspSubmodule F (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) B) ξ ⊥ S Ψ = ⊥ := by sorry
