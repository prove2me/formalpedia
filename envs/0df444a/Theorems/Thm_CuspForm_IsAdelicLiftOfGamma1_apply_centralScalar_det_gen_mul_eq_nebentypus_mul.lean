-- Prove2me | Theorems.Thm_CuspForm_IsAdelicLiftOfGamma1_apply_centralScalar_det_gen_mul_eq_nebentypus_mul
-- name    : CuspForm.IsAdelicLiftOfGamma1.apply_centralScalar_det_gen_mul_eq_nebentypus_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/0968b3da-a0e8-5142-ad61-57e3c4053d66
-- title:
--   Central character of an adelic lift at a good place
-- statement:
--   Fix a nonzero natural number $M$, a Dirichlet character $\varepsilon$ modulo $M$ with values in $\mathbb{C}$, and a cusp form $h$ of weight $2$ on $\Gamma_1(M)$. Assume $h$ has nebentypus $\varepsilon$ in the sense that for every $\gamma \in \mathrm{SL}(2,\mathbb{Z})$ lying in $\Gamma_0(M)$ and every $\tau$ in the upper half-plane, $h(\gamma\tau) = \varepsilon(\gamma_{11} \bmod M)\,(\gamma_{10}\tau + \gamma_{11})^{2} h(\tau)$. Let $\Phi : \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}}) \to \mathbb{C}$ be an adelic lift of $h$, i.e. $\Phi$ is left invariant under the image of $\mathrm{GL}_2(\mathbb{Q})$ under [`AutomorphicForm.globalPoints`](def/AutomorphicForm_AdelicLsXi.html#L15), right invariant under the image under [`AdelicDock.finEmbed`](def/AdelicDock_LocalEmbedding.html#L145) of the level-one subgroup `finiteLevelOne` at the ideal $\mathrm{ratLevel}(M) = (M) \subseteq \mathcal{O}_{\mathbb{Q}}$, and satisfies $\Phi(x) = (h \mid[2]\, \mathrm{ratArchGL2}\,x)(i)$ whenever the finite component `glFin` of $x$ is trivial and its real archimedean component $\mathrm{ratArchGL2}\,x$ has positive determinant. Let $v$ be a height-one prime of $\mathcal{O}_{\mathbb{Q}}$ whose ideal does not divide $(M)$, and let $g \in \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$. Then, writing $\varpi_v$ for the determinant of the Hecke generator at $v$ of the general production pins over $\mathbb{Q}$, which is an idele unit, and embedding it as a central scalar matrix, $$\Phi(\varpi_v \cdot g) = \varepsilon\big(\mathrm{absNorm}(v) \bmod M\big)\,\Phi(g).$$
--
--   This computes the central character of the adelisation of a weight-two form with nebentypus $\varepsilon$: at a place not dividing the level, the central scalar coming from the determinant of the Hecke generator acts by $\varepsilon$ evaluated at the residue norm. It feeds the verification that the adelic lift is a Hecke coset eigenfunction for the general production pins, and the construction of the associated isotypic cusp form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsAdelicLiftOfGamma1_apply_centralScalar_det_gen_mul_eq_nebentypus_mul.lean

import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_AutomorphicForm_CuspidalConstituent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ModularForm

theorem CuspForm.IsAdelicLiftOfGamma1.apply_centralScalar_det_gen_mul_eq_nebentypus_mul
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hε : CuspForm.HasNebentypus ε h)
    {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hΦ : CuspForm.IsAdelicLiftOfGamma1 h Φ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ¬ v.asIdeal ∣ AdelicDock.ratLevel M)
    (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    Φ (centralScalar (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.det ((productionPinsGeneral ℚ).gen v)) * g)
      = ε ((Ideal.absNorm v.asIdeal : ℕ) : ZMod M) * Φ g := by sorry
