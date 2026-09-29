-- Prove2me | Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_exists_forall_norm_a_le_rpow_and_norm_b_le_rpow_of_moderateGrowth
-- name    : AutomorphicForm.SmoothCuspRealizationAt.exists_forall_norm_a_le_rpow_and_norm_b_le_rpow_of_moderateGrowth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/a5bc996a-9cfa-5658-b2d3-d71f379d5a3b
-- title:
--   Polynomial bounds on Hecke eigenvalues from moderate growth
-- statement:
--   Let $F$ be a number field, let $D$ be a set of adelic points of $\mathrm{GL}_2$ over $F$, and let $\Phi$ be a Hecke eigensystem over $\mathbb{C}$ for $F$, that is: a nonzero level ideal $\Phi.\mathrm{level}\subseteq\mathcal{O}_F$ together with functions $a,b$ on the finite places. Let $R$ be a smooth-cusp realization, at the production pins attached to $D$ with level subgroups $N\mapsto \mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, Hecke generators $v\mapsto \mathrm{heckeGen}(v)$, the full central subgroup, the adelic Borel structure with adelic Haar measure on $\mathrm{GL}_2$, and the additive adelic Haar measure conditioned on the box $\mathrm{adelicBox}(F)$, of the raw rescaling $\Phi.\mathrm{toRawCentral}$ of $\Phi$ (same level and same $a$, with $b$ replaced by $v\mapsto (Nv)^{-1}b_v$). Thus $R$ consists of a function $R.\mathrm{toFun}$ on $\mathrm{GL}_2(\mathbb{A}_F)$ that is not identically zero, a central character, the smooth-cusp-automorphic property, invariance under right translation by the level subgroup at $\Phi.\mathrm{level}$, and a finite exceptional set off which $R.\mathrm{toFun}$ is a Hecke coset eigenfunction with eigenvalue $a_v$ and satisfies the central relation with eigenvalue $(Nv)^{-1}b_v$ for the scalar matrix given by $\det \mathrm{heckeGen}(v)$. Assume moderate growth: there are $C\in\mathbb{R}$ and $M\in\mathbb{N}$ with $\|R.\mathrm{toFun}(g)\|\le C\,\max(\|\det g\|,\|\det g\|^{-1})^M$ for all $g$, where $\|\cdot\|$ is the idele norm given by the distributive Haar character on $\mathbb{A}_F$. Then there exists a real $\kappa\ge 0$ such that for every finite place $v$ of $F$ outside the exceptional set of $R$ one has $\|a_v\|\le (Nv)^{\kappa}$ and $\|b_v\|\le (Nv)^{\kappa}$, the exponent being a real power of the absolute norm of $v$.
--
--   This is the trivial (Hecke) bound on the eigenvalues of an automorphic eigensystem, obtained from the Hecke and central relations at a point where the realizing function does not vanish together with moderate growth in the determinant; no Ramanujan-type estimate is asserted. The polynomial bound is what is needed for absolute convergence of the associated Euler product, and it is used in [`AutomorphicForm.exists_differentiable_hasProd_eulerProduct_twist_of_isArithGenuineCuspRealizable`](thm.html#AutomorphicForm.exists_differentiable_hasProd_eulerProduct_twist_of_isArithGenuineCuspRealizable).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_SmoothCuspRealizationAt_exists_forall_norm_a_le_rpow_and_norm_b_le_rpow_of_moderateGrowth.lean

import Definitions.Def_AutomorphicForm_SmoothCuspRealization
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm IsDedekindDomain

theorem AutomorphicForm.SmoothCuspRealizationAt.exists_forall_norm_a_le_rpow_and_norm_b_le_rpow_of_moderateGrowth
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (Φ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
        (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) Φ.toRawCentral)
    (hMG : ∃ C : ℝ, ∃ M : ℕ, ∀ g : AdelicGL2 (𝓞 F) F,
      ‖R.toFun g‖ ≤ C * max (ideleNorm F (Matrix.GeneralLinearGroup.det g))
        (ideleNorm F (Matrix.GeneralLinearGroup.det g))⁻¹ ^ M) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ v : HeightOneSpectrum (𝓞 F), v ∉ R.exceptionalSet →
      ‖Φ.a v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖Φ.b v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ := by sorry
