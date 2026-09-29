-- Prove2me | Theorems.Thm_CuspForm_IsAdelicLiftOfGamma1_apply_mul_finEmbed_eq_inv_nebentypus_mul_of_mem_finiteLevelZero
-- name    : CuspForm.IsAdelicLiftOfGamma1.apply_mul_finEmbed_eq_inv_nebentypus_mul_of_mem_finiteLevelZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/cb5391ab-cc2e-5862-b830-3b82450b3275
-- title:
--   Nebentypus action of K₀(M) on adelic lifts of Γ₁(M)-forms
-- statement:
--   Let $M$ be a nonzero natural number, $\varepsilon$ a Dirichlet character mod $M$ with values in $\mathbb{C}$, and $h$ a cusp form of weight $2$ for $\Gamma_1(M)$ which has nebentypus $\varepsilon$, i.e. $h(\gamma\tau)=\varepsilon(\gamma_{11}\bmod M)\,(\gamma_{10}\tau+\gamma_{11})^{2}h(\tau)$ for all $\gamma\in\mathrm{SL}_2(\mathbb{Z})$ lying in $\Gamma_0(M)$ and all $\tau$ in the upper half-plane. Let $\Phi$ be a complex-valued function on $\mathrm{GL}_2$ of the adele ring of $\mathbb{Q}$ which is an adelic lift of $h$ in the sense of [`CuspForm.IsAdelicLiftOfGamma1`](def/CuspForm_AdelicLiftGamma1.html#L14): $\Phi$ is left invariant under the image of $\mathrm{GL}_2(\mathbb{Q})$ under `globalPoints`, right invariant under the image by [`AdelicDock.finEmbed`](def/AdelicDock_LocalEmbedding.html#L145) of the subgroup `finiteLevelOne` at the ideal $(M)$ of $\mathcal{O}_{\mathbb{Q}}$, and satisfies $\Phi(g)=\bigl(h\mid_{2}\,\mathrm{ratArchGL2}(g)\bigr)(i)$ for every adelic $g$ whose finite component `glFin` is $1$ and whose real component `ratArchGL2` has positive determinant. Let $u\in\mathrm{GL}_2$ of the finite adeles lie in `finiteLevelZero` at the ideal $(M)$, that is, both $u$ and $u^{-1}$ have all entries integral finite adeles and lower-left entry in the ball $\{x:\ v(x)\le \mathrm{idealBound}((M),v)\ \forall v\}$, and let $d$ be an integer with $u_{11}-d$ in that same ball. Then for every $x\in\mathrm{GL}_2$ of the adeles, $\Phi\bigl(x\cdot \mathrm{finEmbed}(u)\bigr)=\varepsilon(d\bmod M)^{-1}\,\Phi(x)$, where $\mathrm{finEmbed}(u)$ is the adelic matrix with identity archimedean component and finite component $u$, and the inverse is taken in $\mathbb{C}$.
--
--   This is the adelic form of the classical dictionary in which $K_0(M)/K_1(M)\cong(\mathbb{Z}/M)^{\times}$ acts on the lift of a form of nebentypus $\varepsilon$ through $\varepsilon^{-1}$ of the lower-right entry; for $\varepsilon$ trivial it reduces to right $K_0(M)$-invariance of the lift of a $\Gamma_0(M)$-form. It is used to extract the central character of the adelic lift and to verify the Hecke-eigenfunction conditions at level $M$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsAdelicLiftOfGamma1_apply_mul_finEmbed_eq_inv_nebentypus_mul_of_mem_finiteLevelZero.lean

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

theorem CuspForm.IsAdelicLiftOfGamma1.apply_mul_finEmbed_eq_inv_nebentypus_mul_of_mem_finiteLevelZero
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hε : CuspForm.HasNebentypus ε h)
    {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hΦ : CuspForm.IsAdelicLiftOfGamma1 h Φ)
    (u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) (hu : u ∈ finiteLevelZero (𝓞 ℚ) ℚ (AdelicDock.ratLevel M))
    (d : ℤ)
    (hd : (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
        - algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (d : ℚ) ∈ idealBall (𝓞 ℚ) ℚ (AdelicDock.ratLevel M))
    (x : AdelicGL2 (𝓞 ℚ) ℚ) :
    Φ (x * AdelicDock.finEmbed (𝓞 ℚ) ℚ u) = (ε (d : ZMod M))⁻¹ * Φ x := by sorry
