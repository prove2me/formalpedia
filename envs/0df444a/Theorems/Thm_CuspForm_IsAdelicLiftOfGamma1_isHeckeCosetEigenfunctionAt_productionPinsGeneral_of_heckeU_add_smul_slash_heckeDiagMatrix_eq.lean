-- Prove2me | Theorems.Thm_CuspForm_IsAdelicLiftOfGamma1_isHeckeCosetEigenfunctionAt_productionPinsGeneral_of_heckeU_add_smul_slash_heckeDiagMatrix_eq
-- name    : CuspForm.IsAdelicLiftOfGamma1.isHeckeCosetEigenfunctionAt_productionPinsGeneral_of_heckeU_add_smul_slash_heckeDiagMatrix_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/0a13e2cc-5add-5aa6-8873-d001bc677a86
-- title:
--   Classical Tₚ eigenvalue transfers to the adelic Hecke operator
-- statement:
--   Let $M$ be a non-zero natural number, $\varepsilon$ a Dirichlet character modulo $M$ with values in $\mathbb{C}$, and $h$ a cusp form of weight $2$ for $\Gamma_1(M)$ satisfying [`CuspForm.HasNebentypus`](def/CuspForm_PrimitiveFormGamma1.html#L13) for $\varepsilon$, i.e. $h(\gamma\cdot\tau)=\varepsilon(\gamma_{11}\bmod M)\,(\gamma_{10}\tau+\gamma_{11})^{2}h(\tau)$ for all $\gamma\in\mathrm{SL}_2(\mathbb{Z})$ lying in $\Gamma_0(M)$ and all $\tau$ in the upper half-plane. Let $\Phi:\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$ be an adelic lift of $h$ in the sense of [`CuspForm.IsAdelicLiftOfGamma1`](def/CuspForm_AdelicLiftGamma1.html#L14): $\Phi$ is left invariant under the image of $\mathrm{GL}_2(\mathbb{Q})$, right invariant under the image under [`AdelicDock.finEmbed`](def/AdelicDock_LocalEmbedding.html#L145) of `finiteLevelOne` at the ideal $(M)$ of $\mathcal{O}_{\mathbb{Q}}$, and at every adele matrix whose finite part is trivial and whose real component lies in $\mathrm{GL}_2^{+}(\mathbb{R})$ its value is $(h\mid_2 g_\infty)(i)$. Let $v$ be a height-one prime of $\mathcal{O}_{\mathbb{Q}}$ with $v$ not dividing $(M)$, put $p=\mathrm{absNorm}(v)$, and let $c\in\mathbb{C}$ satisfy $\sum_{j<p}h\mid_2\bigl(\begin{smallmatrix}p&j\\0&1\end{smallmatrix}\bigr)+\varepsilon(p)\,h\mid_2\mathrm{diag}(p,1)=c\,h$ as functions on the upper half-plane. Then $\Phi$ is a Hecke coset eigenfunction with eigenvalue $c$ for the subgroup that `productionPinsGeneral ℚ` assigns to $(M)$ (the intersection of `levelOne` at $(M)$ with the finite adelic subgroup) and the generator `heckeGen` at $v$: there are $p+1$ elements $r_i$ of $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ lying in the double coset of the generator, whose left cosets $r_iU$ are pairwise distinct and exhaust the double coset, and $\sum_{i}\Phi(g\,r_i)=c\,\Phi(g)$ for every $g$.
--
--   This is the dictionary between the classical Hecke operator $T_p=U_p+\varepsilon(p)\,(\cdot\mid_2\mathrm{diag}(p,1))$ on weight-two forms of level $M$ and nebentypus $\varepsilon$, and the double-coset Hecke operator at $v$ on the adelic lift, transferring the eigenvalue unchanged. It is used by [`CuspForm.IsEigenformWith.isIsotypicCuspFormAt_of_isAdelicLiftOfGamma1`](thm.html#CuspForm.IsEigenformWith.isIsotypicCuspFormAt_of_isAdelicLiftOfGamma1) to identify the adelic Hecke eigensystem of the lift of a classical eigenform.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsAdelicLiftOfGamma1_isHeckeCosetEigenfunctionAt_productionPinsGeneral_of_heckeU_add_smul_slash_heckeDiagMatrix_eq.lean

import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ModularForm

theorem CuspForm.IsAdelicLiftOfGamma1.isHeckeCosetEigenfunctionAt_productionPinsGeneral_of_heckeU_add_smul_slash_heckeDiagMatrix_eq
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hε : CuspForm.HasNebentypus ε h)
    {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hΦ : CuspForm.IsAdelicLiftOfGamma1 h Φ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ¬ v.asIdeal ∣ AdelicDock.ratLevel M) (c : ℂ)
    (hT : ModularForm.heckeU 2 (Ideal.absNorm v.asIdeal) ⇑h
          + ε ((Ideal.absNorm v.asIdeal : ℕ) : ZMod M) •
              ((⇑h) ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix (Ideal.absNorm v.asIdeal))
        = c • ⇑h) :
    SmoothCusp.IsHeckeCosetEigenfunctionAt ℚ ((productionPinsGeneral ℚ).U (AdelicDock.ratLevel M))
      ((productionPinsGeneral ℚ).gen v) v Φ c := by sorry
