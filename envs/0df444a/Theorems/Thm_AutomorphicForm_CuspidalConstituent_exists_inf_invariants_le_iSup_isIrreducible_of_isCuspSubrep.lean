-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_inf_invariants_le_iSup_isIrreducible_of_isCuspSubrep
-- name    : AutomorphicForm.CuspidalConstituent.exists_inf_invariants_le_iSup_isIrreducible_of_isCuspSubrep
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/5e1a90ad-decd-5b66-a6e5-98114cb80871
-- title:
--   Irreducible archimedean types cutting U-invariants in a cuspidal subrepresentation
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers, let $T$ be a finite set of elements of $\mathrm{GL}_2(\mathbb{A}_F)$ (the adelic $\mathrm{GL}_2$ of $F$), and let $\xi$ be a homomorphism from the full subgroup $\top$ of $\mathbb{A}_F^{\times}$ to $\mathbb{C}^{\times}$. Let $U$ be a subgroup of $\mathrm{GL}_2(\mathbb{A}_F)$ with compact underlying set, and $O$ an open subgroup, such that $U = O \sqcap \mathrm{finiteAdelicGL2Subgroup}\,F$, the kernel of the archimedean-component map. Let $\mathrm{tys}$ be an archimedean type family, i.e. a number $\mathrm{card}(w)$ of data at each infinite place $w$ together with representations $\rho$ of the row-isometry group $\mathrm{rowIsometrySubgroup}_0$ of $F_w$ on finite-dimensional complex spaces, and let $V$ be a $\mathbb{C}$-submodule of the space of functions $\mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$. Assume $\mathrm{IsCuspSubrep}$ holds for $V$ relative to $\xi$ and to the production pins attached to the window $D = \bigcup_{x \in T} \mathfrak{S}\,x$, where $\mathfrak{S} = \mathrm{centreCutSiegelSet}\,F\,c\,u\,d_1\,d_2$ consists of those $g$ whose finite part is integral, whose archimedean components have local height at least $c$ and window square at most $u^2$, and whose archimedean determinant norms lie in $[d_1,d_2]$; the pins carry the Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$, central subgroup $\top$, level subgroups $\mathrm{levelOne}(N) \sqcap \mathrm{finiteAdelicGL2Subgroup}\,F$, Hecke generators $\mathrm{heckeGen}$ at the finite places, and the adelic additive Haar measure conditioned on $\mathrm{adelicBox}\,F$. Thus $V$ is contained in the span of the continuous functions all of whose right translates are smooth cuspidal automorphic at these pins with central character $\xi$ and which are of some archimedean type, and $V$ is stable under right translation by finite adelic elements and by archimedean row isometries, and under right convolution by factorisable test functions that are archimedean bi-finite. The conclusion asserts the existence of $n \in \mathbb{N}$ and, for $j \in \{0,\dots,n-1\}$, families $\tau_j = (\tau_j(w))_w$ of archimedean data, one at each infinite place, with every $\tau_j(w).\rho$ irreducible, such that $$V \sqcap (\mathbb{C}^{\mathrm{GL}_2(\mathbb{A}_F)})^U \sqcap \mathrm{archCutSubmodule}\,F\,\mathrm{tys} \le \bigsqcup_{j} \Bigl(V \sqcap (\mathbb{C}^{\mathrm{GL}_2(\mathbb{A}_F)})^U \sqcap \mathrm{archCutSubmodule}\,F\,\langle 1, \tau_j\rangle\Bigr),$$ where $(\mathbb{C}^{\mathrm{GL}_2(\mathbb{A}_F)})^U$ denotes the invariants of the right regular representation restricted along the inclusion of $U$, i.e. the $\varphi$ with $\varphi(xk) = \varphi(x)$ for all $k \in U$; $\mathrm{archCutSubmodule}\,F\,\mathrm{tys}$ is the intersection over infinite places $w$ of the sum over $i < \mathrm{card}(w)$ of the type submodules $\mathrm{archTypeSubmoduleAt}\,F\,w\,(\mathrm{rep}\,w\,i)$; and $\langle 1,\tau_j\rangle$ is the type family with exactly one datum $\tau_j(w)$ at each place, so that its cut is $\bigsqcap_w \mathrm{archTypeSubmoduleAt}\,F\,w\,(\tau_j(w))$. The supremum is a finite join of submodules.
--
--   This is the archimedean refinement step in the analysis of a cuspidal subrepresentation: the part of $V$ which is right invariant under a compact level $U$ contained in the finite-adelic subgroup and which is cut out by an arbitrary family of archimedean types is shown to be covered by finitely many cuts by irreducible types, one at each infinite place. It is used in the proof of finite-dimensionality of level-invariant isotypic pieces of the cuspidal spectrum, and is the generic-compact-level form of the corresponding statement for the level subgroups recorded in the pins.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_inf_invariants_le_iSup_isIrreducible_of_isCuspSubrep.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.CuspidalConstituent.exists_inf_invariants_le_iSup_isIrreducible_of_isCuspSubrep
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (tys : AutomorphicForm.ArchTypeFamily F)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hV : IsCuspSubrep F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ V) :
    ∃ (n : ℕ) (τs : Fin n → ∀ w : InfinitePlace F, ArchRepAt F w),
      (∀ j w, (τs j w).ρ.IsIrreducible) ∧
      V ⊓ Representation.invariants ((rightRegular F).comp U.subtype) ⊓ archCutSubmodule F tys ≤
        ⨆ j : Fin n, V ⊓ Representation.invariants ((rightRegular F).comp U.subtype) ⊓ archCutSubmodule F (⟨fun _ => 1, fun w _ => τs j w⟩ : AutomorphicForm.ArchTypeFamily F) := by sorry
