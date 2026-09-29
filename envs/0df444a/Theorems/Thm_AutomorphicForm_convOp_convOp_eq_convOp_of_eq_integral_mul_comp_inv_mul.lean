-- Prove2me | Theorems.Thm_AutomorphicForm_convOp_convOp_eq_convOp_of_eq_integral_mul_comp_inv_mul
-- name    : AutomorphicForm.convOp_convOp_eq_convOp_of_eq_integral_mul_comp_inv_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/939f801c-4cea-5042-b7a7-74e439f4623a
-- title:
--   Convolution of factorizable test functions on adelic GL₂
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $U$ be a subgroup of $\mathrm{GL}_2(\mathbb{A}_L)$ (the group `AdelicGL2 (𝓞 L) L` of invertible $2\times 2$ matrices over the adele ring of $L$), let $S$ be a finite set of nonzero primes of $\mathcal{O}_K$, and let $\varphi,\psi:\mathrm{GL}_2(\mathbb{A}_L)\to\mathbb{C}$ each be continuous, compactly supported and factorizable in the sense of `IsFactorizableTestFn`: $f(g)=f_\infty(\mathrm{glArch}\,g)\cdot f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ for some compactly supported $f_\infty$ on $\mathrm{GL}_2$ of the infinite adeles which is a $C^\infty$ function of the matrix entries in the mixed space, and some locally constant compactly supported $f_{\mathrm{fin}}$ on $\mathrm{GL}_2$ of the finite adeles. Then for every $\chi$ equal to the convolution $g\mapsto\int\psi(y)\varphi(y^{-1}g)\,dy$ taken against `adelicGLHaar` the following hold. (1) $\chi$ is again continuous, compactly supported and factorizable. (2) For every continuous $w$, $R(\psi)\bigl(R(\varphi)w\bigr)=R(\chi)w$, where $R(f)w:g\mapsto\int w(gx)f(x)\,dx$ is `convOp`. (3) If $\psi(ux)=\psi(x)$ for all $u\in U$ and all $x$, the same holds for $\chi$. (4) If $\varphi(xu)=\varphi(x)$ for all $u\in U$ and all $x$, the same holds for $\chi$. (5) For every family `tys` of archimedean types of $L$ (a finite tuple of representations $\rho$ of `rowIsometrySubgroup₀` at each infinite place), if $x\mapsto\psi(x^{-1})$ lies in `archCutSubmodule`, the infimum over infinite places of the supremum of the type submodules of the $\rho$ in the family, then so does $x\mapsto\chi(x^{-1})$. (6) Likewise, if $\varphi$ lies in the corresponding submodule `archDualCutSubmodule` formed from the dual representations $\rho^\vee$, so does $\chi$. (7) If both $\psi$ and $\varphi$ satisfy `IsUnitFactorizableAbove K L U S`, that is, are two-sided $U$-invariant and admit data $(\,\cdot_a,\cdot_f,\cdot_S)$ satisfying `IsSemiLocalFactorization K L S`, then so does $\chi$.
--
--   This is the statement that factorizable test functions on $\mathrm{GL}_2(\mathbb{A}_L)$ form an algebra under convolution whose action by right convolution operators is multiplicative, together with the stability of level invariance, of the archimedean type conditions and of semi-local factorizability under convolution. It supplies the Hecke-algebra input for the results on isotypic cusp subspaces, namely [`AutomorphicForm.exists_finset_convOp_convOp_eq_sum_on_isotypicCuspSubmodule_inf_archCutSubmodule`](thm.html#AutomorphicForm.exists_finset_convOp_convOp_eq_sum_on_isotypicCuspSubmodule_inf_archCutSubmodule), [`AutomorphicForm.exists_finset_convOp_eq_of_isCuspConstituent_of_ne_zero`](thm.html#AutomorphicForm.exists_finset_convOp_eq_of_isCuspConstituent_of_ne_zero) and [`AutomorphicForm.exists_finset_sum_convOp_eq_self_of_isCuspConstituent`](thm.html#AutomorphicForm.exists_finset_sum_convOp_eq_self_of_isCuspConstituent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_convOp_convOp_eq_convOp_of_eq_integral_mul_comp_inv_mul.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.convOp_convOp_eq_convOp_of_eq_integral_mul_comp_inv_mul
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (U : Subgroup (AdelicGL2 (𝓞 L) L)) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ ψ : AdelicGL2 (𝓞 L) L → ℂ)
    (hφ : IsFactorizableTestFn L φ ∧ Continuous φ ∧ HasCompactSupport φ)
    (hψ : IsFactorizableTestFn L ψ ∧ Continuous ψ ∧ HasCompactSupport ψ) :
    ∀ χ : AdelicGL2 (𝓞 L) L → ℂ,
      χ = (fun g => ∫ y, ψ y * φ (y⁻¹ * g) ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) →
      (IsFactorizableTestFn L χ ∧ Continuous χ ∧ HasCompactSupport χ) ∧
      (∀ w : AdelicGL2 (𝓞 L) L → ℂ, Continuous w → convOp L ψ (convOp L φ w) = convOp L χ w) ∧
      ((∀ u ∈ U, ∀ x, ψ (u * x) = ψ x) → ∀ u ∈ U, ∀ x, χ (u * x) = χ x) ∧
      ((∀ u ∈ U, ∀ x, φ (x * u) = φ x) → ∀ u ∈ U, ∀ x, χ (x * u) = χ x) ∧
      (∀ tys : ArchTypeFamily L,
        (fun x => ψ x⁻¹) ∈ archCutSubmodule L tys → (fun x => χ x⁻¹) ∈ archCutSubmodule L tys) ∧
      (∀ tys : ArchTypeFamily L, φ ∈ archDualCutSubmodule L tys → χ ∈ archDualCutSubmodule L tys) ∧
      (IsUnitFactorizableAbove K L U S ψ → IsUnitFactorizableAbove K L U S φ →
        IsUnitFactorizableAbove K L U S χ) := by sorry
