-- Prove2me | Theorems.Thm_AutomorphicForm_RankinSelberg_exists_finset_norm_whittakerCoefficient_sq_mul_norm_section_le_shell_indicator_of_shell_surgery_of_section_law
-- name    : AutomorphicForm.RankinSelberg.exists_finset_norm_whittakerCoefficient_sq_mul_norm_section_le_shell_indicator_of_shell_surgery_of_section_law
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/239a0fd5-7fe2-530e-98af-3127f7b88872
-- title:
--   Shell majorant for a surgered Whittaker–section integrand
-- statement:
--   Let $K$ be a number field and let $\alpha\colon(\mathbb A_K)^\times\to\mathbb R^\times$ be the character obtained from the distributive Haar character of $\mathbb A_K$ (so that $\alpha(t)$ is the idele norm $\|t\|$), assumed to take positive values. All Whittaker coefficients occurring are `whittakerCoefficient K` for the additive character `stdAddChar K`, parameter $1$, and the carrier data `productionPinsOf` assembled from a set $D_0\subseteq\mathrm{GL}_2(\mathbb A_K)$, the level subgroups $N\mapsto \mathrm{levelOne}\,N\cap\ker(\mathrm{glArch})$, the Hecke generators `heckeGen` and the box `adelicBox K`; concretely $W(f)(g)=\int f(n(u)g)\,\psi(-u)\,d\nu(u)$, with $\nu$ the adelic additive Haar measure conditioned on that box. The data are: a finite set $S$ of finite places of $K$; a character $\omega$ of the ideles with values in $\mathbb C^\times$ and a real $w$ with $\|\omega(z)\|=\|z\|^{w}$; a function $x_0$ on $\mathrm{GL}_2(\mathbb A_K)$, a nonzero ideal $N$, and right invariance of $x_0$ under $\mathrm{levelOne}\,N\cap\ker(\mathrm{glArch})$; an idele $t_0$ whose finite components are $1$ off $S$, an element $k_0$ of $\mathrm{maximalCompactAt}\,K\,S$ (in the adelic maximal compact and with trivial finite component at each $v\notin S$) with $W(x_0)(\mathrm{diag}(t_0,1)k_0)\neq0$, the element $\kappa$ with archimedean part $1$ and finite part that of $k_0$, and integers $a_v$ with $v(t_{0,v})=q_v^{-a_v}$ in the notation $\mathrm{ofAdd}(a_v)$; surgery data $r$, $y\colon\mathrm{Fin}\,r\to\mathbb A_K$ with each $y_i$ having zero archimedean part and zero finite components off $S$, coefficients $c_i\in\mathbb C$ and $m\in\mathbb N$, subject to the multiplier law that for every idele $t$ and every $g'$ commuting with all $n(y_i)$ one has $W\big(g\mapsto\sum_i c_i x_0(g\,n(y_i)\kappa)\big)(\mathrm{diag}(t,1)g')=\big(\sum_i c_i\psi(t y_i)\big)\,W\big(g\mapsto x_0(g\kappa)\big)(\mathrm{diag}(t,1)g')$, to the box law that $\sum_i c_i\psi(ty_i)$ equals the indicator of $\{v(t_v)=\mathrm{ofAdd}(a_v)\ \forall v\in S\}$ whenever $v(t_v)\le \mathrm{ofAdd}(m)$ for all $v\in S$, and to the vanishing of $W(x_0)(\mathrm{diag}(t,1)k\kappa)$ whenever $\mathrm{glFin}\,k=1$, all archimedean components of $k$ are row isometries, and $v(t_v)>\mathrm{ofAdd}(m)$ for some $v\in S$; the surgered vector $x(g)=\sum_i c_i x_0(g\,n(y_i)\kappa)$, left invariant under the global points $\mathrm{GL}_2(K)$, transforming under central scalars by $\omega$, right invariant under $\mathrm{maximalCompactAway}\,K\,S$ and, for some $n>0$, right invariant under lower unipotents $n^-(\gamma)$ for $\gamma$ with zero archimedean part, zero components off $S$ and $v(\gamma_v)\le\mathrm{ofAdd}(-n)$ on $S$; and a family $\varphi\colon\mathbb C\to(\mathrm{GL}_2(\mathbb A_K)\to\mathbb C)$ such that each $\varphi_s$ is an induced section for the pair of characters $\mathrm{etaFst}\,1\,\alpha\,h_\alpha\,s=\|\cdot\|^{s+1/2}$ and $\mathrm{etaSnd}\,1\,\alpha\,h_\alpha\,s=\|\cdot\|^{-(s+1/2)}$ (i.e. $\varphi_s(bg)=\|b_{00}\|^{s+1/2}\|b_{11}\|^{-(s+1/2)}\varphi_s(g)$ for upper triangular $b$), is right invariant under $\mathrm{maximalCompactAway}\,K\,S$, takes only the values $0$ and $1$ on elements with finite part in $\mathrm{finiteIntegralGL2}$ and row-isometric archimedean components, and vanishes on such elements as soon as $v(k_{10,v})>v(k_{11,v})\cdot\mathrm{ofAdd}(-n)$ for some $v\in S$. Assume finally the section law $\varphi_s(\mathrm{diag}(t,1)k)=\|t\|^{s+1/2}\varphi_s(k)$ for all $s$, all $k$ in the adelic maximal compact and all ideles $t$. The conclusion is that there is a finite set $J\subseteq\mathrm{GL}_2(\mathbb A_K)$ all of whose elements have trivial archimedean part, such that for every $s\in\mathbb C$, every $k$ in the adelic maximal compact and every idele $t$ whose finite components are $1$ at all $v\notin S$, $$\|W(x)(\mathrm{diag}(t,1)k)\|^{2}\,\|\varphi_s(\mathrm{diag}(t,1)k)\|\le \mathbf 1\big[v(t_v)=\mathrm{ofAdd}(a_v)\ \forall v\in S\big]\cdot\|t\|^{\operatorname{Re}(s)+1/2}\cdot\sum_{g\in J}\big\|W(x_0)\big(\mathrm{diag}(\mathrm{partAt}\,K\,\emptyset\,t,1)\cdot \mathrm{adelicArchGLIncl}(\mathrm{glArch}\,k)\cdot g\big)\big\|^{2},$$ where $\mathrm{partAt}\,K\,\emptyset\,t$ is the idele with the archimedean part of $t$ and all finite components $1$.
--
--   This is the majorisation step in the Rankin–Selberg analysis of the $S$-part torus integrand: the square of the Whittaker coefficient of a shell-surgered vector, weighted by an induced section, is dominated on the shell by the indicator of the prescribed valuation pattern times a finite sum of archimedean Whittaker values of the original vector. It is the inequality conjunct of [`AutomorphicForm.RankinSelberg.exists_finset_norm_whittakerCoefficient_sq_mul_norm_section_le_shell_indicator_of_shell_surgery`](thm.html#AutomorphicForm.RankinSelberg.exists_finset_norm_whittakerCoefficient_sq_mul_norm_section_le_shell_indicator_of_shell_surgery), with the section law appended as a hypothesis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_RankinSelberg_exists_finset_norm_whittakerCoefficient_sq_mul_norm_section_le_shell_indicator_of_shell_surgery_of_section_law.lean

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

theorem AutomorphicForm.RankinSelberg.exists_finset_norm_whittakerCoefficient_sq_mul_norm_section_le_shell_indicator_of_shell_surgery_of_section_law (K : Type) [Field K] [NumberField K] :
    let α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (S : Finset (HeightOneSpectrum (𝓞 K)))
      (D₀ : Set (AdelicGL2 (𝓞 K) K))
      (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : ℝ)
      (_hω : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ω z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w)

      (x₀ : AdelicGL2 (𝓞 K) K → ℂ) (N : Ideal (𝓞 K)) (_hN : N ≠ ⊥)
      (_hx₀lev : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, x₀ (g * k) = x₀ g)

      (t₀ : (AdeleRing (𝓞 K) K)ˣ) (_ht₀ : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ((t₀ : AdeleRing (𝓞 K) K)).2 v = 1)
      (k₀ : AdelicGL2 (𝓞 K) K) (_hk₀ : k₀ ∈ maximalCompactAt K S)
      (_hWpt : whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne t₀ * k₀) ≠ 0)
      (κ : AdelicGL2 (𝓞 K) K) (_hκ : κ = AdelicDock.finEmbed (𝓞 K) K (glFin (𝓞 K) K k₀))
      (aexp : HeightOneSpectrum (𝓞 K) → ℤ)
      (_haexp : ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) =
        ((Multiplicative.ofAdd (aexp v) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))

      (r : ℕ) (y : Fin r → AdeleRing (𝓞 K) K) (cs : Fin r → ℂ) (m : ℕ)
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

      (x : AdelicGL2 (𝓞 K) K → ℂ) (_hxsum : ∀ g, x g = ∑ i, cs i * x₀ (g * (unipotentGL2 (y i) * κ)))
      (_hxG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g)
      (_hxZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K), x (centralScalar (𝓞 K) K z * g) = ((ω z : ℂˣ) : ℂ) * x g)
      (_hxKS : ∀ k ∈ maximalCompactAway K S, ∀ g : AdelicGL2 (𝓞 K) K, x (g * k) = x g)
      (n : ℕ) (_hn : 0 < n)
      (_hxlow : ∀ (γ : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K), γ.1 = 0 →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → γ.2 v = 0) →
        (∀ v ∈ S, Valued.v (γ.2 v) ≤
          ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        x (g * lowerUnipotentGL2 γ) = x g)

      (φ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 K) K (etaFst 1 α hα s) (etaSnd 1 α hα s) (φ s))
      (_hφKS : ∀ s, ∀ k ∈ maximalCompactAway K S, ∀ g : AdelicGL2 (𝓞 K) K, φ s (g * k) = φ s g)
      (_hφval : ∀ (s : ℂ) (k : AdelicGL2 (𝓞 K) K),
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
          φ s k = 0 ∨ φ s k = 1)
      (_hφsupp : ∀ (s : ℂ) (k : AdelicGL2 (𝓞 K) K),
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
        (∃ v ∈ S, ¬ Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
            Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) *
              ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
          φ s k = 0)
      (hsec : ∀ (s : ℂ) (k : AdelicGL2 (𝓞 K) K), k ∈ adelicMaximalCompact K → ∀ t : (AdeleRing (𝓞 K) K)ˣ,
        φ s (diagOne t * k) = ((NumberField.TateGlobal.ideleNorm K t : ℝ) : ℂ) ^ (s + 1 / 2) * φ s k),
    (∃ J : Finset (AdelicGL2 (𝓞 K) K), (∀ g ∈ J, glArch (𝓞 K) K g = 1) ∧
      ∀ (s : ℂ) (k : AdelicGL2 (𝓞 K) K), k ∈ adelicMaximalCompact K → ∀ t : (AdeleRing (𝓞 K) K)ˣ,
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ((t : AdeleRing (𝓞 K) K)).2 v = 1) →
        ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
          (diagOne t * k)‖ ^ 2 * ‖φ s (diagOne t * k)‖ ≤
          (if ∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) =
              ((Multiplicative.ofAdd (aexp v) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) then (1 : ℝ) else 0) *
            NumberField.TateGlobal.ideleNorm K t ^ (s.re + 1 / 2) *
            ∑ g ∈ J, ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne (NumberField.Idele.partAt K ∅ t) * adelicArchGLIncl K (glArch (𝓞 K) K k) * g)‖ ^ 2) := by sorry
