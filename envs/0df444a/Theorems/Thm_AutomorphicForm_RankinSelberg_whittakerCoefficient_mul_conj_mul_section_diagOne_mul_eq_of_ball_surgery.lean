-- Prove2me | Theorems.Thm_AutomorphicForm_RankinSelberg_whittakerCoefficient_mul_conj_mul_section_diagOne_mul_eq_of_ball_surgery
-- name    : AutomorphicForm.RankinSelberg.whittakerCoefficient_mul_conj_mul_section_diagOne_mul_eq_of_ball_surgery
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/794dc64a-9736-5a6a-893f-9601d66701ac
-- title:
--   Pointwise torus evaluation of a ball-surgered Rankin–Selberg integrand
-- statement:
--   Throughout, $K$ is a number field, $S$ a finite set of finite places of $K$, and $\alpha$ denotes the homomorphism from the ideles of $K$ to $\mathbb{R}^\times$ obtained from the module character `distribHaarChar (AdeleRing (𝓞 K) K)` by pushing its $\mathbb{R}_{\ge 0}$-values into $\mathbb{R}$ and landing in the units; the hypothesis `hα` asserts $\alpha(t)>0$ for every idele $t$. Write $\iota_{\mathrm{fin}}$ for [`AdelicDock.finEmbed`](def/AdelicDock_LocalEmbedding.html#L145), the embedding of $GL_2$ of the finite adeles into $GL_2$ of the adeles with archimedean part $1$, $\iota_\infty$ for `adelicArchGLIncl`, the embedding of $GL_2$ of the infinite adeles with finite part $1$, $n(u)$ for `unipotentGL2 u` $=\begin{pmatrix}1&u\\0&1\end{pmatrix}$, $n^-(\gamma)$ for `lowerUnipotentGL2 γ`, and $\mathrm{diag}(t,1)$ for `diagOne t`. For a function $f$ on $GL_2$ of the adeles and a point $g$, write $W[f](g)$ for
--   $$W[f](g)=\mathtt{whittakerCoefficient}\,K\,P\,\psi_K\,f\,1\,g,$$
--   where $\psi_K$ is the standard adelic additive character [`NumberField.StandardAddChar.stdAddChar K`](def/NumberField_AdelicTraceFin.html#L198) and $P$ is the carrier-pins record `productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`; by definition this is $\int f(n(z)g)\,\psi_K(-z)\,\mathrm{d}\nu(z)$ with $\nu$ the additive adelic Haar measure conditioned on the box `adelicBox K` (of the pins only the measure component enters the Whittaker coefficient). The symbol $\le \mathrm{ofAdd}(c)$ below abbreviates the corresponding inequality for `Valued.v` in `WithZero (Multiplicative ℤ)`.
--
--   The data are: the window $D_0 \subseteq GL_2$ of the adeles; idele characters $\omega_x,\omega_y,\nu$ with values in $\mathbb{C}^\times$ and a real number $w$, subject to the compatibility `hων`: $\omega_x(z)\,\overline{\omega_y(z)}\,\nu(z)=\|z\|^{2w}$ for every idele $z$, where $\|z\|$ is [`NumberField.TateGlobal.ideleNorm K z`](def/NumberField_TateGlobalZeta.html#L19).
--
--   A function $x_0$ on $GL_2$ of the adeles and an integer $n_b>0$ are given, with the congruence invariance `hx₀cong`: $x_0(gk)=x_0(g)$ for every $g$ and every $k$ with trivial archimedean part (i.e. $k \in$ `finiteAdelicGL2Subgroup K`, the kernel of `glArch`), with finite part in `finiteIntegralGL2 (𝓞 K) K` (matrix and inverse both level-zero at the unit ideal), with trivial component at every finite place outside $S$, and with all entries of $k-1$ of valuation $\le \mathrm{ofAdd}(-n_b)$ at every $v\in S$.
--
--   An idele $t_0$ is given with archimedean component $1$, components $1$ at all finite places outside $S$, and, for an integer $m$, valuation $\le \mathrm{ofAdd}(m)$ at every $v \in S$ (`ht₀box`). Also given are $k_0 \in$ `maximalCompactAt K S` (integral finite part, row-isometric archimedean components, trivial component outside $S$) and $\kappa = \iota_{\mathrm{fin}}(\mathrm{glFin}(k_0))$, the purely finite element attached to $k_0$.
--
--   The ball-surgery data consist of $r \in \mathbb{N}$, adeles $u_i$ and complex scalars $c_i$ for $i \in \mathrm{Fin}\,r$, with: `husupp`, each $u_i$ has zero archimedean component and zero component at every finite place outside $S$; `hWmult`, for every idele $t$ and every $g'$ commuting with all $n(u_i)$,
--   $$W\Big[g \mapsto \sum_i c_i\,x_0\big(g\,n(u_i)\,\kappa\big)\Big](\mathrm{diag}(t,1)g') = \Big(\sum_i c_i\,\psi_K(t\,u_i)\Big)\,W\big[g \mapsto x_0(g\kappa)\big](\mathrm{diag}(t,1)g');$$
--   `hμball`, for every idele $t$ whose valuation at each $v\in S$ is $\le \mathrm{ofAdd}(m)$, the multiplier $\sum_i c_i\,\psi_K(t\,u_i)$ equals $1$ if $\mathrm{v}(t_v-t_{0,v}) \le \mathrm{v}(t_{0,v})\cdot\mathrm{ofAdd}(-n_b)$ for all $v\in S$, and $0$ otherwise; and `hboxvan`, for every $k$ with trivial finite part and row-isometric archimedean components at all infinite places and every idele $t$ whose valuation exceeds $\mathrm{ofAdd}(m)$ at some $v \in S$, one has $W[x_0](\mathrm{diag}(t,1)\,k\,\kappa)=0$.
--
--   The first vector $x$ is a function on $GL_2$ of the adeles with: `hxsum`, $x(g)=\sum_i c_i\,x_0\big(g\,(n(u_i)\kappa)\big)$; `hxG`, left invariance under the image of $GL_2(K)$; `hxZ`, central character $\omega_x$, i.e. $x(z\cdot g)=\omega_x(z)x(g)$ for central scalars $z$; `hxKS`, right invariance under `maximalCompactAway K S` (integral, trivial archimedean part, trivial components at the places of $S$); and, for an integer $n>0$, `hxlow`, right invariance under the lower unipotents $n^-(\gamma)$ with $\gamma$ having zero archimedean component, zero components outside $S$, and valuation $\le \mathrm{ofAdd}(-n)$ at each $v \in S$.
--
--   The second vector $y$ is a function with: `hyG`, left $GL_2(K)$-invariance; `hyZ`, central character $\omega_y$; `hyKS`, right `maximalCompactAway K S`-invariance; `hycong`, the same depth-$n_b$ congruence invariance at $S$ as imposed on $x_0$; and `hylow`, the same depth-$n$ lower-unipotent invariance as imposed on $x$.
--
--   Finally, a function $f_\infty$ (`finf`) and a family of sections $\varphi_s$ (`φ`) are given with: `hφ`, for every $s$ the function $\varphi_s$ satisfies `IsInducedSection` for the pair of characters `etaFst 1 α hα s` $= \alpha^{\,s+1/2}$ and `etaSnd ν α hα s` $= \nu\,\alpha^{-(s+1/2)}$, that is $\varphi_s(bg)=\alpha(b_{00})^{s+1/2}\,\nu(b_{11})\alpha(b_{11})^{-(s+1/2)}\varphi_s(g)$ for $b$ in the adelic Borel subgroup; `hφKS`, right `maximalCompactAway K S`-invariance of each $\varphi_s$; `hφsupp`, $\varphi_s(k)=0$ whenever $k$ has finite part in `finiteIntegralGL2`, row-isometric archimedean components, and the bottom-row condition fails at some $v\in S$, i.e. $\mathrm{v}(k_{10,v}) \le \mathrm{v}(k_{11,v})\cdot\mathrm{ofAdd}(-n)$ does not hold; and `hφval`, for all $s$, all such $k$, every $k_\infty$ with trivial finite part and the same archimedean part as $k$, and every family of local units $d_v$ ($v$ a finite place) with $k_{11,v}=d_v$ for $v \in S$, if the bottom-row condition $\mathrm{v}(k_{10,v}) \le \mathrm{v}(k_{11,v})\cdot\mathrm{ofAdd}(-n)$ holds at every $v\in S$ then $\varphi_s(k)=\big(\prod_{v\in S}(\mathtt{localChar}\ \nu\ v)(d_v)\big)\,f_\infty(k_\infty)$.
--
--   Given in addition $s \in \mathbb{C}$ and $k \in$ `adelicMaximalCompact K` (finite part in `finiteIntegralGL2 (𝓞 K) K`, and archimedean component at each infinite place a row isometry in the sense of `IsRowIsometry`: determinant of norm $1$ and preservation of the sum of squared norms of row vectors), the assertion is that there exists an idele $\rho$ such that:
--
--   (i) the archimedean component of $\rho$ is $1$;
--
--   (ii) $\rho_v = 1$ at every finite place $v \notin S$;
--
--   (iii) $\mathrm{v}(\rho_v)=1$ at every $v \in S$;
--
--   (iv) for every idele $t$ with $t_v = 1$ at every finite place $v \notin S$,
--   $$W[x](\mathrm{diag}(t,1)k)\cdot\overline{W[y](\mathrm{diag}(t,1)k)}\cdot\varphi_s(\mathrm{diag}(t,1)k)$$
--   equals $0$ unless the bottom-row condition $\mathrm{v}(k_{10,v}) \le \mathrm{v}(k_{11,v})\cdot\mathrm{ofAdd}(-n)$ holds at every $v\in S$, in which case it equals
--   $$\|t\|^{\,s+1/2}\, f_\infty\big(\iota_\infty(\mathrm{glArch}(k))\big)\cdot\Big(\text{the ball factor}\Big),$$
--   where $\|t\|$ is [`NumberField.TateGlobal.ideleNorm K t`](def/NumberField_TateGlobalZeta.html#L19) raised to the complex power $s+1/2$, and the ball factor is $0$ unless $\mathrm{v}\big((t\rho)_v - t_{0,v}\big) \le \mathrm{v}(t_{0,v})\cdot\mathrm{ofAdd}(-n_b)$ holds at every $v \in S$, in which case it equals
--   $$W[x_0]\Big(\mathrm{diag}\big(\mathtt{partAt}\,K\,\emptyset\,t,1\big)\,\iota_\infty(\mathrm{glArch}(k))\,\big(\mathrm{diag}(t_0,1)\,\kappa\big)\Big)\cdot\overline{W[y]\Big(\mathrm{diag}\big(\mathtt{partAt}\,K\,\emptyset\,t,1\big)\,\iota_\infty(\mathrm{glArch}(k))\,\mathrm{diag}(t_0,1)\Big)}.$$
--   Here [`NumberField.Idele.partAt K ∅ t`](def/NumberField_IdeleProductMeasure.html#L90) is the idele with the archimedean part of $t$ and finite part truncated at the empty set of finite places. Note that the second, conjugated, inner Whittaker coefficient is that of $y$ itself and its argument carries no factor $\kappa$, while the first is that of $x_0$ and does.
--
--   This is the pointwise evaluation, at a fixed element $k$ of the adelic maximal compact subgroup and a fixed torus parameter, of the integrand occurring in the bad-place ($S$-) part of a Rankin–Selberg integral of two $GL_2$ automorphic vectors, the first of which has been replaced by a finite linear combination of right translates (a ball surgery) whose Whittaker multiplier is the indicator of a ball around $t_0$. It is used by [`AutomorphicForm.RankinSelberg.exists_integral_torus_pair_eq_mul_integral_archTorus_of_ball_surgery`](thm.html#AutomorphicForm.RankinSelberg.exists_integral_torus_pair_eq_mul_integral_archTorus_of_ball_surgery) and [`AutomorphicForm.RankinSelberg.lintegral_torus_pair_lt_top_of_ball_surgery`](thm.html#AutomorphicForm.RankinSelberg.lintegral_torus_pair_lt_top_of_ball_surgery), which integrate the resulting expression over the idele class torus and bound it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_RankinSelberg_whittakerCoefficient_mul_conj_mul_section_diagOne_mul_eq_of_ball_surgery.lean

import Definitions.Def_AutomorphicForm_RankinSelbergQuotientIntegral
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ArchType
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain
open scoped ENNReal NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

theorem AutomorphicForm.RankinSelberg.whittakerCoefficient_mul_conj_mul_section_diagOne_mul_eq_of_ball_surgery
    (K : Type) [Field K] [NumberField K] :
    let α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (S : Finset (HeightOneSpectrum (𝓞 K)))
      (D₀ : Set (AdelicGL2 (𝓞 K) K))

      (ωx ωy : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : ℝ)
      (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hων : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((ωx z : ℂˣ) : ℂ) * (starRingEnd ℂ) ((ωy z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) =
          ((NumberField.TateGlobal.ideleNorm K z ^ (2 * w) : ℝ) : ℂ))

      (x₀ : AdelicGL2 (𝓞 K) K → ℂ)
      (nb : ℕ) (_hnb : 0 < nb)
      (_hx₀cong : ∀ (g k : AdelicGL2 (𝓞 K) K), k ∈ finiteAdelicGL2Subgroup K →
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → finComponent (𝓞 K) K v (glFin (𝓞 K) K k) = 1) →
        (∀ v ∈ S, ∀ i j : Fin 2,
          Valued.v ((((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j -
              (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
            ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        x₀ (g * k) = x₀ g)

      (t₀ : (AdeleRing (𝓞 K) K)ˣ) (_ht₀inf : ((t₀ : AdeleRing (𝓞 K) K)).1 = 1)
      (_ht₀ : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ((t₀ : AdeleRing (𝓞 K) K)).2 v = 1)
      (m : ℕ)
      (_ht₀box : ∀ v ∈ S, Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
        ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
      (k₀ : AdelicGL2 (𝓞 K) K) (_hk₀ : k₀ ∈ maximalCompactAt K S)
      (κ : AdelicGL2 (𝓞 K) K) (_hκ : κ = AdelicDock.finEmbed (𝓞 K) K (glFin (𝓞 K) K k₀))

      (r : ℕ) (u : Fin r → AdeleRing (𝓞 K) K) (cs : Fin r → ℂ)
      (_husupp : ∀ i, (u i).1 = 0 ∧ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → (u i).2 v = 0)
      (_hWmult : ∀ (t : (AdeleRing (𝓞 K) K)ˣ) (g' : AdelicGL2 (𝓞 K) K),
        (∀ i, g' * unipotentGL2 (u i) = unipotentGL2 (u i) * g') →
        whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (fun g => ∑ i, cs i * x₀ (g * unipotentGL2 (u i) * κ)) 1
          (diagOne t * g') =
          (∑ i, cs i * NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * u i)) *
            whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (fun g => x₀ (g * κ)) 1
          (diagOne t * g'))
      (_hμball : ∀ t : (AdeleRing (𝓞 K) K)ˣ,
        (∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) ≤
            ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        (∑ i, cs i * NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * u i)) =
          if ∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
              Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) *
                ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) then 1 else 0)
      (_hboxvan : ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
        ∀ t : (AdeleRing (𝓞 K) K)ˣ,
          (∃ v ∈ S, ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) <
            Valued.v (((t : AdeleRing (𝓞 K) K)).2 v)) →
          whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne t * k * κ) = 0)

      (x : AdelicGL2 (𝓞 K) K → ℂ) (_hxsum : ∀ g, x g = ∑ i, cs i * x₀ (g * (unipotentGL2 (u i) * κ)))
      (_hxG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g)
      (_hxZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K), x (centralScalar (𝓞 K) K z * g) = ((ωx z : ℂˣ) : ℂ) * x g)
      (_hxKS : ∀ k ∈ maximalCompactAway K S, ∀ g : AdelicGL2 (𝓞 K) K, x (g * k) = x g)
      (n : ℕ) (_hn : 0 < n)
      (_hxlow : ∀ (γ : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K), γ.1 = 0 →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → γ.2 v = 0) →
        (∀ v ∈ S, Valued.v (γ.2 v) ≤
          ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        x (g * lowerUnipotentGL2 γ) = x g)

      (y : AdelicGL2 (𝓞 K) K → ℂ)
      (_hyG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), y (globalPoints (𝓞 K) K γ * g) = y g)
      (_hyZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K), y (centralScalar (𝓞 K) K z * g) = ((ωy z : ℂˣ) : ℂ) * y g)
      (_hyKS : ∀ k ∈ maximalCompactAway K S, ∀ g : AdelicGL2 (𝓞 K) K, y (g * k) = y g)
      (_hycong : ∀ (g k : AdelicGL2 (𝓞 K) K), k ∈ finiteAdelicGL2Subgroup K →
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → finComponent (𝓞 K) K v (glFin (𝓞 K) K k) = 1) →
        (∀ v ∈ S, ∀ i j : Fin 2,
          Valued.v ((((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j -
              (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
            ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        y (g * k) = y g)
      (_hylow : ∀ (γ : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K), γ.1 = 0 →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → γ.2 v = 0) →
        (∀ v ∈ S, Valued.v (γ.2 v) ≤
          ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        y (g * lowerUnipotentGL2 γ) = y g)

      (finf : AdelicGL2 (𝓞 K) K → ℂ)
      (φ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 K) K (etaFst 1 α hα s) (etaSnd ν α hα s) (φ s))
      (_hφKS : ∀ s, ∀ k ∈ maximalCompactAway K S, ∀ g : AdelicGL2 (𝓞 K) K, φ s (g * k) = φ s g)
      (_hφsupp : ∀ (s : ℂ) (k : AdelicGL2 (𝓞 K) K),
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
        (∃ v ∈ S, ¬ Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
            Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) *
              ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
          φ s k = 0)
      (_hφval : ∀ (s : ℂ) (k kinf : AdelicGL2 (𝓞 K) K) (d : (v : HeightOneSpectrum (𝓞 K)) → (v.adicCompletion K)ˣ),
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
        glFin (𝓞 K) K kinf = 1 → glArch (𝓞 K) K kinf = glArch (𝓞 K) K k →
        (∀ v ∈ S, (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) = (d v : v.adicCompletion K)) →
        (∀ v ∈ S, Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
            Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) *
              ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
          φ s k = (∏ v ∈ S, ((localChar ν v (d v) : ℂˣ) : ℂ)) * finf kinf)
      (s : ℂ) (k : AdelicGL2 (𝓞 K) K) (_hk : k ∈ adelicMaximalCompact K),
    ∃ ρ : (AdeleRing (𝓞 K) K)ˣ, ((ρ : AdeleRing (𝓞 K) K)).1 = 1 ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ((ρ : AdeleRing (𝓞 K) K)).2 v = 1) ∧
      (∀ v ∈ S, Valued.v (((ρ : AdeleRing (𝓞 K) K)).2 v) = 1) ∧
      ∀ t : (AdeleRing (𝓞 K) K)ˣ, (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ((t : AdeleRing (𝓞 K) K)).2 v = 1) →
        whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
          (diagOne t * k) *
            (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne t * k)) *
            φ s (diagOne t * k) =
          (if (∀ v ∈ S, Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
              Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) * ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) then
            ((NumberField.TateGlobal.ideleNorm K t : ℝ) : ℂ) ^ (s + 1 / 2) *
              finf (adelicArchGLIncl K (glArch (𝓞 K) K k)) *
              (if (∀ v ∈ S, Valued.v ((((t * ρ) : AdeleRing (𝓞 K) K)).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
              Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) * ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) then
                whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne (NumberField.Idele.partAt K ∅ t) * adelicArchGLIncl K (glArch (𝓞 K) K k) * (diagOne t₀ * κ)) *
                  (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne (NumberField.Idele.partAt K ∅ t) * adelicArchGLIncl K (glArch (𝓞 K) K k) * diagOne t₀))
               else 0)
           else 0) := by sorry
