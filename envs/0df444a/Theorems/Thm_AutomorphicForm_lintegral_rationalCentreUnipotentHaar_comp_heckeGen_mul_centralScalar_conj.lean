-- Prove2me | Theorems.Thm_AutomorphicForm_lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj
-- name    : AutomorphicForm.lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/714e8ac7-d482-5813-842b-978c012c6052
-- title:
--   Conjugation by the Hecke element scales the Z(K)N measure by Nv
-- statement:
--   Let $K$ be a number field with ring of integers $\mathcal{O}_K$, let $v$ be a nonzero prime of $\mathcal{O}_K$, and let $u$ be a unit of the adele ring of $K$. Write $b =$ `heckeGen` $\cdot$ `centralScalar` $u$ in $\mathrm{GL}_2$ of the adeles, where the first factor is the image under `diagOne` of the unit attached to a uniformizer of $v$, placed at the place $v$ only (so $b$ is $\mathrm{diag}(\varpi_v,1)$ at $v$ times the scalar matrix $u$), and let $H$ be the subgroup `rationalCentreUnipotent` $K$, the join of the group of scalar matrices with entries in $K^\times$ (embedded diagonally in the adelic points) and the group of adelic upper unipotent matrices. Assume $b$ normalises $H$ in the strong form that for every $y$ in $\mathrm{GL}_2$ of the adeles one has $y \in H$ if and only if $b y b^{-1} \in H$. Then for every measurable $F \colon H \to [0,\infty]$, the lower Lebesgue integral of $x \mapsto F(b x b^{-1})$ over $H$, with respect to the measure `rationalCentreUnipotentHaar` $K$ — the sum over $a \in K^\times$ of the translates by the scalar matrix $a$ of the measure on the adelic unipotent group obtained by transporting the adelic additive Haar measure normalised to give the adelic box total mass $1$ — equals $\mathrm{absNorm}(v)$ times the integral of $F$ over $H$ with respect to the same measure.
--
--   This is the computation of the module of conjugation by the Hecke element at $v$ on $Z(K)N(\mathbb{A}_K)$: the adelic modulus of multiplication by a uniformizer idele at $v$ is $Nv^{-1}$, so the change of variables produces the factor $Nv$. It supplies the weight relating consecutive Iwasawa shells at $v$ in the Rankin–Selberg computation, and is cited in [`AutomorphicForm.RankinSelberg.exists_hasProd_quotientIntegral_eq_sPartIntegral_mul_of_shell_recursion`](thm.html#AutomorphicForm.RankinSelberg.exists_hasProd_quotientIntegral_eq_sPartIntegral_mul_of_shell_recursion).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj.lean

import Definitions.Def_AutomorphicForm_RationalCentreUnipotentQuotient
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm IsDedekindDomain
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem AutomorphicForm.lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hb : ∀ y : AdelicGL2 (𝓞 K) K, y ∈ rationalCentreUnipotent K ↔
      (heckeGen (𝓞 K) K v * centralScalar (𝓞 K) K u) * y * (heckeGen (𝓞 K) K v * centralScalar (𝓞 K) K u)⁻¹ ∈
        rationalCentreUnipotent K)
    (F : rationalCentreUnipotent K → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F ⟨(heckeGen (𝓞 K) K v * centralScalar (𝓞 K) K u) * (x : AdelicGL2 (𝓞 K) K) *
        (heckeGen (𝓞 K) K v * centralScalar (𝓞 K) K u)⁻¹, (hb (x : AdelicGL2 (𝓞 K) K)).mp x.2⟩
      ∂(rationalCentreUnipotentHaar K) =
      (Ideal.absNorm v.asIdeal : ℝ≥0∞) * ∫⁻ x, F x ∂(rationalCentreUnipotentHaar K) := by sorry
