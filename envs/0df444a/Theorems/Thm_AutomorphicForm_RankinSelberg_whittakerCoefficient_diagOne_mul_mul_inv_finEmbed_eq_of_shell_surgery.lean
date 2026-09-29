-- Prove2me | Theorems.Thm_AutomorphicForm_RankinSelberg_whittakerCoefficient_diagOne_mul_mul_inv_finEmbed_eq_of_shell_surgery
-- name    : AutomorphicForm.RankinSelberg.whittakerCoefficient_diagOne_mul_mul_inv_finEmbed_eq_of_shell_surgery
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/f878820e-f7e7-5fb4-ab99-1d66c7d042de
-- title:
--   Shell surgery preserves the Whittaker coefficient at diag(t₀,1)k₀
-- statement:
--   Let $K$ be a number field, $S$ a finite set of finite places of $K$, $D_0$ a subset of $\mathrm{GL}_2(\mathbb{A}_K)$ and $x_0 \colon \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$; throughout, $W_1\varphi(g)$ denotes the Whittaker coefficient $\int \varphi(n(x)g)\,\psi(-x)\,d\nu(x)$ at $\alpha=1$, formed with the standard additive character $\psi$ of $\mathbb{A}_K$ and with the data `productionPinsOf` built from $D_0$, the level subgroups $v\mapsto$ `levelOne` intersected with the kernel of the archimedean part, the Hecke generators `heckeGen`, and the conditioning set `adelicBox K`, so that $\nu$ is adelic additive Haar measure conditioned on that box. Let $t_0$ be an idele unit and $k_0$ an element of `maximalCompactAt K S`, that is, $k_0$ has integral finite part, all its archimedean components are row isometries, and its finite component is trivial at every $v\notin S$; assume $W_1x_0(\mathrm{diag}(t_0,1)k_0)\ne 0$. Let $\kappa$ be the adelic matrix with archimedean part $1$ and finite part that of $k_0$, and let $a_v\in\mathbb{Z}$ satisfy $v(t_{0,v})=\mathrm{ofAdd}(a_v)$ for all finite $v$. Let $r\in\mathbb{N}$, $y\colon \mathrm{Fin}\,r\to\mathbb{A}_K$, $c\colon \mathrm{Fin}\,r\to\mathbb{C}$ and $m\in\mathbb{N}$ be such that: each $y_i$ has vanishing archimedean part and vanishing component at every $v\notin S$; for every idele unit $t$ and every $g'$ commuting with all $n(y_i)$ one has $W_1\bigl(\sum_i c_i\,x_0(\,\cdot\,n(y_i)\kappa)\bigr)(\mathrm{diag}(t,1)g') = \bigl(\sum_i c_i\,\psi(t\,y_i)\bigr)\,W_1\bigl(x_0(\,\cdot\,\kappa)\bigr)(\mathrm{diag}(t,1)g')$; for every $t$ with $v(t_v)\le \mathrm{ofAdd}(m)$ for all $v\in S$ the multiplier $\sum_i c_i\,\psi(t\,y_i)$ equals $1$ if $v(t_v)=\mathrm{ofAdd}(a_v)$ for all $v\in S$ and $0$ otherwise; and for every $k$ with trivial finite part and row-isometric archimedean components and every $t$ with $\mathrm{ofAdd}(m)<v(t_v)$ for some $v\in S$ one has $W_1x_0(\mathrm{diag}(t,1)k\kappa)=0$. Then for the surgered vector $x(g)=\sum_i c_i\,x_0\bigl(g\,(n(y_i)\kappa)\bigr)$ one has $W_1x\bigl(\mathrm{diag}(t_0,1)(k_0\kappa^{-1})\bigr) = W_1x_0\bigl(\mathrm{diag}(t_0,1)k_0\bigr)$.
--
--   The statement records the effect of a shell surgery on the first Whittaker coefficient: replacing $x_0$ by the finite linear combination of right translates $x_0(\,\cdot\,n(y_i)\kappa)$ leaves the coefficient at the chosen non-degenerate torus point unchanged, up to the compensating right translation by $\kappa^{-1}$. It provides one conjunct of [`AutomorphicForm.RankinSelberg.exists_finset_norm_whittakerCoefficient_sq_mul_norm_section_le_shell_indicator_of_shell_surgery`](thm.html#AutomorphicForm.RankinSelberg.exists_finset_norm_whittakerCoefficient_sq_mul_norm_section_le_shell_indicator_of_shell_surgery), in the Rankin–Selberg estimates for adelic $\mathrm{GL}_2$ Whittaker coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_RankinSelberg_whittakerCoefficient_diagOne_mul_mul_inv_finEmbed_eq_of_shell_surgery.lean

import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ArchType
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain
open scoped ENNReal NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

theorem AutomorphicForm.RankinSelberg.whittakerCoefficient_diagOne_mul_mul_inv_finEmbed_eq_of_shell_surgery (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (D₀ : Set (AdelicGL2 (𝓞 K) K))
    (x₀ : AdelicGL2 (𝓞 K) K → ℂ)
    (t₀ : (AdeleRing (𝓞 K) K)ˣ)
    (k₀ : AdelicGL2 (𝓞 K) K)
    (_hk₀ : k₀ ∈ maximalCompactAt K S)
    (_hWpt : whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne t₀ * k₀) ≠ 0)
    (κ : AdelicGL2 (𝓞 K) K)
    (_hκ : κ = AdelicDock.finEmbed (𝓞 K) K (glFin (𝓞 K) K k₀))
    (aexp : HeightOneSpectrum (𝓞 K) → ℤ)
    (_haexp : ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) =
        ((Multiplicative.ofAdd (aexp v) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (r : ℕ)
    (y : Fin r → AdeleRing (𝓞 K) K)
    (cs : Fin r → ℂ)
    (m : ℕ)
    (_hysupp : ∀ i, (y i).1 = 0 ∧ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → (y i).2 v = 0)
    (_hWmult : ∀ (t : (AdeleRing (𝓞 K) K)ˣ) (g' : AdelicGL2 (𝓞 K) K),
        (∀ i, g' * unipotentGL2 (y i) = unipotentGL2 (y i) * g') →
        whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (fun g => ∑ i, cs i * x₀ (g * unipotentGL2 (y i) * κ)) 1
          (diagOne t * g') =
          (∑ i, cs i * NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * y i)) *
            whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (fun g => x₀ (g * κ)) 1
          (diagOne t * g'))
    (_hμbox : ∀ t : (AdeleRing (𝓞 K) K)ˣ,
        (∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) ≤
            ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        (∑ i, cs i * NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * y i)) =
          if ∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) =
              ((Multiplicative.ofAdd (aexp v) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) then 1 else 0)
    (_hboxvan : ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
        ∀ t : (AdeleRing (𝓞 K) K)ˣ,
          (∃ v ∈ S, ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) <
            Valued.v (((t : AdeleRing (𝓞 K) K)).2 v)) →
          whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne t * k * κ) = 0)
    (x : AdelicGL2 (𝓞 K) K → ℂ)
    (_hxsum : ∀ g, x g = ∑ i, cs i * x₀ (g * (unipotentGL2 (y i) * κ))) :
    whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
          (diagOne t₀ * (k₀ * κ⁻¹)) =
      whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne t₀ * k₀) := by sorry
