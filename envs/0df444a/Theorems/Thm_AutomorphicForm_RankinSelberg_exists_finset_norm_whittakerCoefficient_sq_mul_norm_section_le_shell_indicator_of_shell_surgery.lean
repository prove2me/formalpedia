-- Prove2me | Theorems.Thm_AutomorphicForm_RankinSelberg_exists_finset_norm_whittakerCoefficient_sq_mul_norm_section_le_shell_indicator_of_shell_surgery
-- name    : AutomorphicForm.RankinSelberg.exists_finset_norm_whittakerCoefficient_sq_mul_norm_section_le_shell_indicator_of_shell_surgery
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/9aeeb473-6a29-519a-ad11-d77b299549aa
-- title:
--   Section law, shell majorant and base value after shell surgery
-- statement:
--   Throughout, $K$ is a number field; $\mathrm{GL}_2(\mathbb{A}_K)$ denotes `AdelicGL2 (𝓞 K) K`, the group of units of the $2\times 2$ matrices over the adele ring, $\mathrm{diag}(t,1)$ denotes `diagOne t`, $u(y)=\begin{pmatrix}1&y\\0&1\end{pmatrix}$ denotes `unipotentGL2 y`, $u^-(\gamma)=\begin{pmatrix}1&0\\\gamma&1\end{pmatrix}$ denotes `lowerUnipotentGL2 γ`, and $\|t\| =$ [`NumberField.TateGlobal.ideleNorm K t`](def/NumberField_TateGlobalZeta.html#L19) is the real number given by the distributive Haar character of $\mathbb{A}_K$ at the idele $t$. The monoid homomorphism $\alpha$ introduced by the `let` is that same distributive Haar character, viewed through $\mathbb{R}_{\ge 0}\to\mathbb{R}$ and as a homomorphism into $\mathbb{R}^\times$; the hypothesis $h\alpha$ asserts $0 < \alpha(t)$ for every idele $t$.
--
--   For every function $f$ on $\mathrm{GL}_2(\mathbb{A}_K)$ the symbol $W f(g)$ abbreviates `whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) f 1 g`, that is the integral $\int f(u(z)g)\,\psi(-z)$ taken with respect to the carrier datum `productionPinsOf`: its measure on $\mathbb{A}_K$ is the adelic additive Haar measure conditioned on `adelicBox K` (adeles whose archimedean part lies in the fundamental-domain box and whose finite part is everywhere integral), its distinguished set is $D_0$, its central subgroup is $\top$, its level subgroups are $N\mapsto$ `levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K` and its Hecke elements are the `heckeGen (𝓞 K) K v`; the additive character is `stdAddChar K` and the field element indexing the character is $1$.
--
--   The data quantified over are: a finite set $S$ of maximal ideals of $\mathcal{O}_K$; a set $D_0\subseteq \mathrm{GL}_2(\mathbb{A}_K)$; a character $\omega$ of the ideles into $\mathbb{C}^\times$ and a real number $w$ with $|\omega(z)| = \|z\|^{w}$ for all ideles $z$; a function $x_0 : \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ and a nonzero ideal $N$ of $\mathcal{O}_K$ such that $x_0$ is right invariant under `levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K` (elements whose finite part satisfies the level-one condition at $N$, together with its inverse, and whose archimedean part is trivial); an idele $t_0$ whose finite component is $1$ at every $v\notin S$; an element $k_0 \in$ `maximalCompactAt K S`, i.e. $k_0$ has finite part in `finiteIntegralGL2 (𝓞 K) K` and row-isometric archimedean components at every infinite place (the determinant has norm $1$ and the row action preserves $|x|^2+|y|^2$), and trivial component at every finite $v \notin S$; the non-degeneracy hypothesis $W x_0(\mathrm{diag}(t_0,1)k_0)\neq 0$; the element $\kappa =$ [`AdelicDock.finEmbed (𝓞 K) K (glFin (𝓞 K) K k₀)`](def/AdelicDock_LocalEmbedding.html#L145), the element of $\mathrm{GL}_2(\mathbb{A}_K)$ with the same finite part as $k_0$ and trivial archimedean part; and a function $a : v \mapsto a_v \in \mathbb{Z}$ with $\mathrm{val}_v(t_{0,v}) = \mathrm{ofAdd}(a_v)$ in $\mathbb{Z}_{\ge}\cup\{0\}$-notation (`WithZero (Multiplicative ℤ)`) for every finite place $v$.
--
--   The shell-surgery data are $r\in\mathbb{N}$, adeles $y_i$ ($i\in \mathrm{Fin}\,r$), complex scalars $c_i$, and $m\in\mathbb{N}$, subject to four hypotheses. Support: each $y_i$ has zero archimedean part and zero finite component at every $v \notin S$. Multiplier law: for every idele $t$ and every $g'$ commuting with all $u(y_i)$, one has $W\bigl(g\mapsto \sum_i c_i x_0(g\,u(y_i)\,\kappa)\bigr)(\mathrm{diag}(t,1)g') = \bigl(\sum_i c_i\,\psi(t\,y_i)\bigr)\, W\bigl(g\mapsto x_0(g\kappa)\bigr)(\mathrm{diag}(t,1)g')$, with $\psi =$ `stdAddChar K`. Shell indicator on the box: for every idele $t$ with $\mathrm{val}_v(t_v)\le \mathrm{ofAdd}(m)$ at all $v\in S$, the multiplier $\sum_i c_i\,\psi(t\,y_i)$ equals $1$ if $\mathrm{val}_v(t_v)=\mathrm{ofAdd}(a_v)$ for all $v\in S$ and $0$ otherwise. Vanishing above the box: for every $k$ with trivial finite part and row-isometric archimedean components at all infinite places, and every idele $t$ with $\mathrm{ofAdd}(m) < \mathrm{val}_v(t_v)$ for some $v\in S$, one has $W x_0(\mathrm{diag}(t,1)\,k\,\kappa) = 0$.
--
--   The surgered vector is a function $x : \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ with $x(g) = \sum_i c_i\,x_0\bigl(g\,(u(y_i)\kappa)\bigr)$, left invariant under the image of $\mathrm{GL}_2(K)$ under `globalPoints`, transforming under the central scalars by $x(\mathrm{scalar}(z)g) = \omega(z)\,x(g)$, right invariant under `maximalCompactAway K S` (finite part integral, archimedean part trivial, component trivial at every $v\in S$), and, for an integer $n>0$, right invariant under the lower unipotents $u^-(\gamma)$ for all adeles $\gamma$ with zero archimedean part, zero finite component off $S$, and $\mathrm{val}_v(\gamma_v)\le \mathrm{ofAdd}(-n)$ at every $v\in S$.
--
--   The sections are a family $\varphi : \mathbb{C}\to(\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C})$ such that, for every $s$, $\varphi_s$ is an induced section for the pair of characters `etaFst 1 α hα s` and `etaSnd 1 α hα s`, namely $\varphi_s(bg) = \alpha(b_{00})^{s+1/2}\,\alpha(b_{11})^{-(s+1/2)}\,\varphi_s(g)$ for all $b$ in the adelic Borel subgroup (lower-left entry zero) and all $g$; each $\varphi_s$ is right invariant under `maximalCompactAway K S`; each $\varphi_s$ takes the value $0$ or $1$ at every $k$ whose finite part lies in `finiteIntegralGL2 (𝓞 K) K` and whose archimedean components are row isometries; and each such $\varphi_s$ vanishes at such a $k$ whenever there is $v\in S$ with $\mathrm{val}_v(k_{10,v}) \le \mathrm{val}_v(k_{11,v})\cdot\mathrm{ofAdd}(-n)$ failing.
--
--   Under these hypotheses three assertions hold.
--
--   First, the section law: for every $s\in\mathbb{C}$, every $k \in$ `adelicMaximalCompact K` and every idele $t$, $\varphi_s(\mathrm{diag}(t,1)k) = \|t\|^{\,s+1/2}\,\varphi_s(k)$, the power being the complex power of the real number $\|t\|$ viewed in $\mathbb{C}$.
--
--   Second, the shell majorant through finitely many finite translates: there exists a finite set $J\subseteq \mathrm{GL}_2(\mathbb{A}_K)$ with $\mathrm{glArch}(g)=1$ for all $g\in J$ such that for every $s\in\mathbb{C}$, every $k\in$ `adelicMaximalCompact K` and every idele $t$ whose finite component is $1$ at every $v\notin S$,
--   $$\bigl|W x(\mathrm{diag}(t,1)k)\bigr|^{2}\,\bigl|\varphi_s(\mathrm{diag}(t,1)k)\bigr| \;\le\; \mathbf{1}\bigl[\mathrm{val}_v(t_v)=\mathrm{ofAdd}(a_v)\ \forall v\in S\bigr]\cdot \|t\|^{\,\mathrm{Re}(s)+1/2}\cdot \sum_{g\in J}\bigl|W x_0\bigl(\mathrm{diag}(t',1)\,\iota(\mathrm{glArch}(k))\,g\bigr)\bigr|^{2},$$
--   where $\mathbf{1}[\cdot]$ is the indicated shell indicator ($1$ if the condition holds, $0$ otherwise), $t' =$ [`NumberField.Idele.partAt K ∅ t`](def/NumberField_IdeleProductMeasure.html#L90) is the idele obtained from $t$ by the truncation of its finite part to the empty set of places, keeping the archimedean part, and $\iota =$ `adelicArchGLIncl K` embeds $\mathrm{GL}_2$ of the infinite adeles into $\mathrm{GL}_2(\mathbb{A}_K)$ with trivial finite part.
--
--   Third, the value at the non-degenerate point: $W x\bigl(\mathrm{diag}(t_0,1)\,(k_0\kappa^{-1})\bigr) = W x_0\bigl(\mathrm{diag}(t_0,1)k_0\bigr)$.
--
--   This is the pointwise, non-archimedean half of the analysis of the $S$-part of a Rankin–Selberg torus integral for $\mathrm{GL}_2$ over a number field: it records the homogeneity of the induced section along the torus, bounds the square of the Whittaker coefficient of the shell-surgered vector against a shell indicator times finitely many archimedean translates of the Whittaker coefficient of the original vector, and identifies the value of the surgered Whittaker coefficient at the chosen non-degenerate torus point. It combines the section law `section_diagOne_mul_eq_ideleNorm_cpow_mul_of_isInducedSection_etaFst_etaSnd`, the majorant `exists_finset_norm_whittakerCoefficient_sq_mul_norm_section_le_shell_indicator_of_shell_surgery_of_section_law` and the base-point identity `whittakerCoefficient_diagOne_mul_mul_inv_finEmbed_eq_of_shell_surgery`, and feeds the analyticity and positivity statement `analyticOnNhd_sPartIntegral_and_pos_of_shell_surgery`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_RankinSelberg_exists_finset_norm_whittakerCoefficient_sq_mul_norm_section_le_shell_indicator_of_shell_surgery.lean

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

theorem AutomorphicForm.RankinSelberg.exists_finset_norm_whittakerCoefficient_sq_mul_norm_section_le_shell_indicator_of_shell_surgery
    (K : Type) [Field K] [NumberField K] :
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
          φ s k = 0),
    (∀ (s : ℂ) (k : AdelicGL2 (𝓞 K) K), k ∈ adelicMaximalCompact K → ∀ t : (AdeleRing (𝓞 K) K)ˣ,
        φ s (diagOne t * k) = ((NumberField.TateGlobal.ideleNorm K t : ℝ) : ℂ) ^ (s + 1 / 2) * φ s k) ∧
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
          (diagOne (NumberField.Idele.partAt K ∅ t) * adelicArchGLIncl K (glArch (𝓞 K) K k) * g)‖ ^ 2) ∧
    whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
          (diagOne t₀ * (k₀ * κ⁻¹)) =
      whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne t₀ * k₀) := by sorry
