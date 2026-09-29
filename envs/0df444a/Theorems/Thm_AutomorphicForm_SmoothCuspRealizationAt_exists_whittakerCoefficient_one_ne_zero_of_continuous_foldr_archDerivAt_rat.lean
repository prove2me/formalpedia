-- Prove2me | Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_exists_whittakerCoefficient_one_ne_zero_of_continuous_foldr_archDerivAt_rat
-- name    : AutomorphicForm.SmoothCuspRealizationAt.exists_whittakerCoefficient_one_ne_zero_of_continuous_foldr_archDerivAt_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/afdd0156-6af2-5b43-aa71-41a646ba7761
-- title:
--   Non-vanishing first Whittaker coefficient over ℚ
-- statement:
--   Fix a set $D \subseteq \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ and a complex Hecke eigensystem $\Theta$ over $\mathbb{Q}$, that is, a nonzero level ideal $\Theta.\mathrm{level} \subseteq \mathcal{O}_{\mathbb{Q}}$ together with families of complex numbers $a_v, b_v$ indexed by the finite places. The carrier data is `productionPinsOf` for $\mathbb{Q}$ with window $D$, with level subgroups $N \mapsto \mathrm{levelOne}(N) \sqcap$ `finiteAdelicGL2Subgroup` (the kernel of the archimedean projection), with Hecke generators $v \mapsto \mathrm{heckeGen}(v)$, and with the box `adelicBox ℚ`; its central subgroup is all of the units, its group measure is the adelic Haar measure on $\mathrm{GL}_2$, and its unipotent measure $\nu$ is the adelic additive Haar measure conditioned on `adelicBox ℚ`. Let $R$ be a smooth cusp realisation at these pins for $\Theta$: a function $R.\mathrm{toFun} \colon \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}}) \to \mathbb{C}$ that is not identically zero, is a smooth cuspidal automorphic function for some central character, is right invariant under the level subgroup attached to $\Theta.\mathrm{level}$, and outside a finite exceptional set of places is a Hecke coset eigenfunction with eigenvalue $a_v$ and satisfies the central relation with factor $b_v$. Assume further: $R.\mathrm{toFun}$ is continuous (the predicate `IsGenuineCuspRealizationAt`); it is archimedean-smooth at the real place of $\mathbb{Q}$, i.e. for every $g$ the map $e \mapsto R.\mathrm{toFun}(g \cdot \mathrm{archRealLiftAt}(e))$ on $2 \times 2$ real matrices is $C^\infty$ on the locus $\det e \ne 0$; and for every finite list $l$ of directions in $\{H, E, F\}$ the iterated flow derivative of $R.\mathrm{toFun}$ along $l$ (each step being $g \mapsto \frac{d}{dt}\big|_{t=0} \varphi(g \cdot \mathrm{archFlowAt}(d,t))$) is continuous. Then there exists $g \in \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ with $$\int R.\mathrm{toFun}(u(x) g)\, \psi(-x) \, d\nu(x) \ne 0,$$ where $\psi$ is the standard adelic additive character of $\mathbb{Q}$ and $u(x)$ the upper unipotent matrix; that is, the Whittaker coefficient of index $\alpha = 1$ does not vanish identically.
--
--   This is the first step towards the Whittaker (Kirillov) model of an adelic cusp form: the Fourier expansion of a cuspidal function along the unipotent radical has a nonvanishing coefficient of nonzero index, and translating by a diagonal element moves that index to $1$. It is used in the Langlands–Tunnell part of the development, where the archimedean behaviour of the Whittaker coefficient of index one is matched against the archimedean parameter of a weight-one constituent.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_SmoothCuspRealizationAt_exists_whittakerCoefficient_one_ne_zero_of_continuous_foldr_archDerivAt_rat.lean

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open LanglandsTunnell LanglandsTunnell.RealArchParam
open LanglandsTunnell.Converse

theorem AutomorphicForm.SmoothCuspRealizationAt.exists_whittakerCoefficient_one_ne_zero_of_continuous_foldr_archDerivAt_rat
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (Θ : HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) Θ)
    (hR : IsGenuineCuspRealizationAt ℚ (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) Θ R)
    (hsm : IsArchSmoothAt Rat.isReal_infinitePlace R.toFun)
    (hreg : ∀ l : List ArchDir, Continuous (l.foldr (archDerivAt Rat.isReal_infinitePlace) R.toFun)) :
    ∃ g : AdelicGL2 (𝓞 ℚ) ℚ,
      whittakerCoefficient ℚ (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) (NumberField.StandardAddChar.stdAddChar ℚ) R.toFun 1 g ≠ 0 := by sorry
