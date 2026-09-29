-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_inf_eq_bot_or_le_of_isCuspConstituent_principal
-- name    : AutomorphicForm.CuspidalConstituent.inf_eq_bot_or_le_of_isCuspConstituent_principal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/1bcdb65e-53ca-5a17-8de6-78841494084d
-- title:
--   Minimality transfer at principal level for cuspidal constituents
-- statement:
--   Let $F$ be a number field, $D$ a subset of $\mathrm{GL}_2(\mathbb{A}_F)$, $\xi$ a homomorphism from the full subgroup $\top$ of $\mathbb{A}_F^{\times}$ to $\mathbb{C}^{\times}$, $N \neq 0$ an ideal of $\mathcal{O}_F$, and $tys$ a family assigning to each infinite place $w$ of $F$ a number $\mathrm{card}\,w$ of archimedean types $\mathrm{rep}\,w\,i$ at $w$. Throughout, the pins are those produced by `productionPinsOf` from $D$, from the level structure $N \mapsto \mathrm{principalLevel}(N) \cap \ker(\mathrm{glArch})$ (the finite part of the principal congruence subgroup), from the Hecke generators $\mathrm{heckeGen}_v$ and from the adelic box; their central subgroup is $\top$, their measures being adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$ and additive Haar measure conditioned on the box. Let $V$ be a $\mathbb{C}$-submodule of the functions $\mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ which is a cuspidal constituent for these pins and $\xi$: it satisfies `IsCuspSubrep`, is nonzero, and every `IsCuspSubrep` submodule contained in it is either $\bot$ or $V$ itself. Let $M$ be a further $\mathbb{C}$-submodule subject to three stability hypotheses: (i) $M$ is stable under right translation by $\mathrm{rowIsometryInclAt_0}\,w\,k$ for every infinite place $w$ and every $k$ in the row-isometry subgroup of $\mathrm{GL}_2(F_w)$; (ii) for every $g$ in the finite part $\ker(\mathrm{glArch})$ and every finite family $\mathrm{reps} : \mathrm{Fin}\,n \to \mathrm{GL}_2(\mathbb{A}_F)$ which is a system of representatives of the right $U(N)$-cosets in the double coset $U(N)\,g\,U(N)$ — each $\mathrm{reps}\,i$ of the form $u g u'$ with $u, u' \in U(N)$, each such $x$ equal to $\mathrm{reps}\,i \cdot u$ for some $i$ and $u \in U(N)$, and $\mathrm{reps}\,i^{-1}\mathrm{reps}\,j \in U(N)$ only for $i = j$ — the function $x \mapsto \sum_i \varphi(x \cdot \mathrm{reps}\,i)$ lies in $M$ for every $\varphi$ in $M$ that is right $U(N)$-invariant; (iii) $M$ is stable under right convolution $\mathrm{rightConv}\,\varphi\,f$ by every factorizable test function $f$ which is arch bi-finite for $tys$ and satisfies $f(ux) = f(x) = f(xu)$ for all $u \in U(N)$. Then the intersection of $V$ with the submodule of right $U(N)$-invariant functions and with the archimedean cut $\bigsqcap_w \bigsqcup_{i} \mathrm{archTypeSubmoduleAt}\,w\,(\mathrm{rep}\,w\,i)$ either meets $M$ in $0$, or is contained in $M$.
--
--   This is a Schur-type minimality statement: the level-$N$, type-$tys$ cut of an irreducible cuspidal constituent admits no proper intersection with a subspace stable under the right translations, Hecke double-coset operators and convolutions that preserve the cut, the level structure being given here by full principal congruence subgroups. It is used in establishing that right convolution acts by scalars on level-spherical vectors of a given type at principal level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_inf_eq_bot_or_le_of_isCuspConstituent_principal.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.CuspidalConstituent.inf_eq_bot_or_le_of_isCuspConstituent_principal
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily F)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : IsCuspConstituent F (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ V)
    (M : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hMk : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion),
      ∀ φ ∈ M, rightTranslate F (rowIsometryInclAt₀ F w k) φ ∈ M)
    (hMhecke : ∀ g ∈ finiteAdelicGL2Subgroup F, ∀ (n : ℕ) (reps : Fin n → AdelicGL2 (𝓞 F) F),
      (∀ i, ∃ u ∈ (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, ∃ u' ∈ (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, reps i = u * g * u') →
      (∀ x : AdelicGL2 (𝓞 F) F, (∃ u ∈ (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, ∃ u' ∈ (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, x = u * g * u') →
        ∃ i, ∃ u ∈ (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, x = reps i * u) →
      (∀ i j, (reps i)⁻¹ * reps j ∈ (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N → i = j) →
      ∀ φ ∈ M ⊓ levelInvariantSubmodule F (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N,
        (fun x => ∑ i, φ (x * reps i)) ∈ M)
    (hMconv : ∀ f : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f → IsArchBiFinite F tys f →
      (∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, f (u * x) = f x ∧ f (x * u) = f x) →
      ∀ φ ∈ M, rightConv F φ f ∈ M) :
    V ⊓ levelInvariantSubmodule F (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N ⊓ archCutSubmodule F tys ⊓ M = ⊥ ∨
      V ⊓ levelInvariantSubmodule F (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N ⊓ archCutSubmodule F tys ≤ M := by sorry
