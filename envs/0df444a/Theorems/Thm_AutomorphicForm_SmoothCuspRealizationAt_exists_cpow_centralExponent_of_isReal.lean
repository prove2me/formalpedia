-- Prove2me | Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_exists_cpow_centralExponent_of_isReal
-- name    : AutomorphicForm.SmoothCuspRealizationAt.exists_cpow_centralExponent_of_isReal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/d16c3e53-c639-5216-b310-ae690aa821b2
-- title:
--   Central exponent at a real place: positive scalars act by t^{c₀}
-- statement:
--   Let $F$ be a number field, let $D$ be an arbitrary subset of $\mathrm{GL}_2(\mathbb{A}_F)$, and let $\Theta$ be a complex Hecke eigensystem for $F$, i.e. a nonzero level ideal $\Theta.\mathrm{level}\subset\mathcal{O}_F$ together with families of complex Hecke and central eigenvalues $a_v,b_v$ indexed by the finite places. Fix the carrier data `productionPinsOf` built from $D$: Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$ with its Borel structure, full central subgroup $Z=\top$ inside $(\mathbb{A}_F)^\times$, level subgroups $N\mapsto \mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, Hecke generators $\mathrm{heckeGen}(v)$, and the adelic additive measure conditioned on `adelicBox`. Let $R$ be a smooth cuspidal realisation of $\Theta$ at these data: a function $R.\mathrm{toFun}:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$, not identically zero, with a central character on $Z$, satisfying the smooth cuspidality condition, right invariance under the level subgroup at $\Theta.\mathrm{level}$, and, outside a finite exceptional set of places, the Hecke coset eigenvalue relations with eigenvalue $a_v$ and the central relations with eigenvalue $b_v$. Assume $R$ is genuine, i.e. $R.\mathrm{toFun}$ is continuous, and let $w$ be a real infinite place of $F$. Then there exists $c_0\in\mathbb{C}$ such that for every unit $t$ of $\mathbb{R}$ with $t>0$ and every $g\in\mathrm{GL}_2(\mathbb{A}_F)$, $$R.\mathrm{toFun}\bigl(\iota_w(t\cdot 1_2)\,g\bigr)=t^{c_0}\,R.\mathrm{toFun}(g),$$ where $\iota_w(t\cdot 1_2)$ is the scalar matrix $t$ transported along the inverse of the isomorphism $F_w\cong\mathbb{R}$ attached to the real place $w$ and placed in the component at $w$ of the archimedean part of $\mathrm{GL}_2(\mathbb{A}_F)$, and $t^{c_0}$ is the principal complex power.
--
--   This isolates the archimedean exponent of the central character of a continuous cuspidal realisation at a real place: the central character is a continuous idele class quasicharacter, whose component at a real place has the form $x\mapsto |x|^{u}\operatorname{sgn}(x)^{a}$, and on positive scalars only the exponent $u=c_0$ survives. It supplies the central exponent used by [`AutomorphicForm.exists_forall_archOccursInClassOf_and_centralExponent`](thm.html#AutomorphicForm.exists_forall_archOccursInClassOf_and_centralExponent) and by [`AutomorphicForm.one_le_of_archOccursInClassOf_isArchLoweringAnnihilatedAt_of_coversModCentre`](thm.html#AutomorphicForm.one_le_of_archOccursInClassOf_isArchLoweringAnnihilatedAt_of_coversModCentre).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_SmoothCuspRealizationAt_exists_cpow_centralExponent_of_isReal.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_ArchType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.SmoothCuspRealizationAt.exists_cpow_centralExponent_of_isReal
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))
    (Θ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      Θ)
    (hR : IsGenuineCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      Θ R)
    (w : InfinitePlace F) (hw : w.IsReal) :
    ∃ c₀ : ℂ, ∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 F) F,
      R.toFun (adelicArchGLInclAt F w
          (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
            (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = (((t : ℝ) : ℂ) ^ c₀) * R.toFun g := by sorry
