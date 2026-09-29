-- Prove2me | Theorems.Thm_AutomorphicForm_RankinSelberg_exists_integral_torus_pair_eq_mul_integral_archTorus_of_ball_surgery
-- name    : AutomorphicForm.RankinSelberg.exists_integral_torus_pair_eq_mul_integral_archTorus_of_ball_surgery
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/5ebdaf46-6986-545c-8de2-7ac5ec21b434
-- title:
--   Ball-surgered torus integral evaluated past the centre
-- statement:
--   Let $K$ be a number field. Write $\alpha$ for the homomorphism $(\mathbb{A}_K)^\times \to \mathbb{R}^\times$ obtained from the module character `distribHaarChar (AdeleRing (𝓞 K) K)` by composing with the inclusion $\mathbb{R}_{\ge 0} \to \mathbb{R}$ and passing to units, and let `hα` assert that all its values are positive. Throughout, $\|\cdot\|$ denotes [`NumberField.TateGlobal.ideleNorm K`](def/NumberField_TateGlobalZeta.html#L19), the real number $\mathrm{distribHaarChar}(\mathbb{A}_K)(t)$; $W_1 f(g)$ denotes `whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) f 1 g`, i.e. the integral $\int f(u(x)g)\,\psi(-x)$ of $f$ against the standard global additive character $\psi$ along the upper unipotent, taken with respect to additive Haar measure on $\mathbb{A}_K$ conditioned to the box `adelicBox K`; and $\mathrm{diag}(t,1)$ denotes `diagOne t`. The carrier data entering the Whittaker coefficient are a set $D_0 \subseteq \mathrm{GL}_2(\mathbb{A}_K)$, the level subgroups $N \mapsto$ `levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`, the Hecke elements `heckeGen (𝓞 K) K v` and the box `adelicBox K`.
--
--   The data are: a finite set $S$ of finite places of $K$; the set $D_0$; characters $\omega_x,\omega_y : (\mathbb{A}_K)^\times \to \mathbb{C}^\times$ and a real number $w$ with $|\omega_x(z)| = |\omega_y(z)| = \|z\|^w$ for all $z$ (hypotheses `_hωx`, `_hωy`); a character $\nu$ with $\omega_x(z)\,\overline{\omega_y(z)}\,\nu(z) = \|z\|^{2w}$ (hypothesis `_hων`); a continuous function $x_0$ on $\mathrm{GL}_2(\mathbb{A}_K)$ (`_hx₀c`); a positive natural number $n_b$ (`_hnb`).
--
--   The hypotheses on $x_0$ are: `_hx₀cong`, right invariance $x_0(gk) = x_0(g)$ for every $k$ with trivial archimedean part (i.e. $k \in$ `finiteAdelicGL2Subgroup K`, the kernel of `glArch`) whose finite part lies in `finiteIntegralGL2 (𝓞 K) K` (the matrices which, together with their inverses, satisfy the level-zero condition at the unit ideal), whose component at every $v \notin S$ is trivial, and all of whose entries satisfy $v(k_{ij} - \delta_{ij}) \le \mathrm{ofAdd}(-n_b)$ for $v \in S$; and `_hxlarge`, rapid decay: for each $g$ with trivial archimedean part and each $M \in \mathbb{N}$ there is $C_g$ with $\|W_1x_0(\mathrm{diag}(a,1)\,k\,g)\| \le C_g\,\|a\|^{w/2}\,|a_{\mathrm{pl}}|^{-M}$ for all $k$ with trivial finite part whose archimedean components are row isometries in the sense of `IsRowIsometry` (determinant of norm $1$ and preservation of the sum of squared norms under the row action), all ideles $a$ with trivial finite part, and all infinite places $\mathrm{pl}$.
--
--   The surgery data are: an idele $t_0$ with trivial infinite part (`_ht₀inf`) and trivial components outside $S$ (`_ht₀`), and $m \in \mathbb{N}$ with $v(t_0) \le \mathrm{ofAdd}(m)$ for $v \in S$ (`_ht₀box`); an element $k_0$ of `maximalCompactAt K S` (the adelic maximal compact subgroup intersected with the kernels of the components at all $v \notin S$), and $\kappa =$ [`AdelicDock.finEmbed (𝓞 K) K (glFin (𝓞 K) K k₀)`](def/AdelicDock_LocalEmbedding.html#L145), the adelic matrix with archimedean part $1$ and finite part that of $k_0$; an integer $r$, adeles $u_1,\dots,u_r$ and complex numbers $c_1,\dots,c_r$ with each $u_i$ of zero infinite part and zero components outside $S$ (`_husupp`). Three hypotheses tie these together: `_hWmult`, that for every idele $t$ and every $g'$ commuting with all $u(u_i)$, the Whittaker coefficient of $g \mapsto \sum_i c_i x_0(g\,u(u_i)\,\kappa)$ at $\mathrm{diag}(t,1)g'$ equals $\bigl(\sum_i c_i \psi(t\,u_i)\bigr)$ times that of $g \mapsto x_0(g\kappa)$ at $\mathrm{diag}(t,1)g'$; `_hμball`, that for every idele $t$ with $v(t) \le \mathrm{ofAdd}(m)$ at all $v \in S$ the sum $\sum_i c_i \psi(t\,u_i)$ equals $1$ if $v(t - t_0) \le v(t_0)\,\mathrm{ofAdd}(-n_b)$ for all $v \in S$ and $0$ otherwise; and `_hboxvan`, that $W_1x_0(\mathrm{diag}(t,1)\,k\,\kappa) = 0$ whenever $k$ has trivial finite part and row-isometric archimedean components and $\mathrm{ofAdd}(m) < v(t)$ for some $v \in S$.
--
--   The first vector is a function $x$ with $x(g) = \sum_i c_i x_0\bigl(g\,(u(u_i)\kappa)\bigr)$ (`_hxsum`), continuous (`_hxc`), left invariant under the global points `globalPoints (𝓞 K) K γ`, $\gamma \in \mathrm{GL}_2(K)$ (`_hxG`), transforming by $\omega_x$ under the central scalars (`_hxZ`), right invariant under `maximalCompactAway K S` (the adelic maximal compact subgroup intersected with the kernel of `glArch` and with the kernels of the components at all $v \in S$) (`_hxKS`), and, for a positive natural number $n$ (`_hn`), right invariant under the lower unipotents `lowerUnipotentGL2 γ` for adeles $\gamma$ with zero infinite part, zero components outside $S$, and $v(\gamma) \le \mathrm{ofAdd}(-n)$ for $v \in S$ (`_hxlow`).
--
--   The second vector is a function $y$ which is continuous (`_hyc`), left invariant under the global points (`_hyG`), transforms by $\omega_y$ under the central scalars (`_hyZ`), is right invariant under `maximalCompactAway K S` (`_hyKS`), satisfies the same congruence invariance at depth $n_b$ as $x_0$ does (`_hycong`), is right invariant under the lower unipotents of depth $n$ as above (`_hylow`), and satisfies the rapid-decay bound `_hylarge` with the same shape as `_hxlarge`, with $y$ in place of $x_0$.
--
--   The section data are: a continuous function $f_\infty$ on $\mathrm{GL}_2(\mathbb{A}_K)$ (`_hfc`) and a family $\varphi : \mathbb{C} \to \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ such that, for every $s$, $\varphi_s$ is an induced section for the pair of characters `etaFst 1 α hα s` $= \alpha^{s+1/2}$ and `etaSnd ν α hα s` $= \nu\,\alpha^{-(s+1/2)}$, i.e. $\varphi_s(bg) = \alpha(b_{00})^{s+1/2}\,\bigl(\nu\alpha^{-(s+1/2)}\bigr)(b_{11})\,\varphi_s(g)$ for $b$ in the adelic Borel subgroup (`_hφ`); the map $(s,g) \mapsto \varphi_s(g)$ is continuous (`_hφjc`); each $\varphi_s$ is right invariant under `maximalCompactAway K S` (`_hφKS`); $\varphi_s(k) = 0$ whenever the finite part of $k$ is integral, its archimedean components are row isometries, and for some $v \in S$ the inequality $v(k_{10}) \le v(k_{11})\,\mathrm{ofAdd}(-n)$ fails (`_hφsupp`); and `_hφval`, the value formula: for all $s$, all $k$ with integral finite part and row-isometric archimedean components, all $k_\infty$ with trivial finite part and the same archimedean part as $k$, and all families $d = (d_v)_v$ of local units such that $(k_{11})_v = d_v$ for $v \in S$, if $v(k_{10}) \le v(k_{11})\,\mathrm{ofAdd}(-n)$ for all $v \in S$ then $\varphi_s(k) = \bigl(\prod_{v \in S} \mathrm{localChar}\,\nu\,v\,(d_v)\bigr)\,f_\infty(k_\infty)$, where `localChar ν v` is $\nu$ restricted to the ideles supported at $v$.
--
--   Finally there are decay exponents and constants: $\delta_x > 0$ and $C_x$ with
--   $$\bigl\|W_1x_0\bigl(\mathrm{diag}(a,1)\,k\,(\mathrm{diag}(t_0,1)\kappa)\bigr)\bigr\| \le C_x \prod_{\mathrm{pl}} |a_{\mathrm{pl}}|^{\mathrm{pl.mult}\cdot w/2}\,\bigl(\min(1,|a_{\mathrm{pl}}|)\bigr)^{\delta_x}$$
--   for all $k$ with trivial finite part and row-isometric archimedean components and all ideles $a$ with trivial finite part (`_hδx`, `_hCx`), and $\delta_y > 0$, $C_y$ with the same bound for $W_1y$ at $\mathrm{diag}(a,1)\,k\,\mathrm{diag}(t_0,1)$ and exponent $\delta_y$ (`_hδy`, `_hCy`).
--
--   Under these hypotheses the assertion is that there exists a real number $\kappa_0 > 0$ such that for every $s \in \mathbb{C}$ with $\mathrm{Re}\,s > 1/2 - (\delta_x + \delta_y)/2$,
--   $$\int \Bigl(\int W_1x\bigl(\mathrm{diag}(t,1)k\bigr)\,\overline{W_1y\bigl(\mathrm{diag}(t,1)k\bigr)}\,\varphi_s\bigl(\mathrm{diag}(t,1)k\bigr)\,\|t\|^{-w-1}\,d\,\mathrm{maximalCompactHaar}\,K(k)\Bigr)\,d\,\mathrm{sPartMeasure}\,K\,S(t)$$
--   equals
--   $$\kappa_0\,\bigl(\|t_0\|^{\,s+1/2}\,\|t_0\|^{-w-1}\bigr)\int f_\infty(k)\Bigl(\int \|a\|^{\,s+1/2}\,\|a\|^{-w-1}\,W_1x_0\bigl(\mathrm{diag}(a,1)\,k\,(\mathrm{diag}(t_0,1)\kappa)\bigr)\,\overline{W_1y\bigl(\mathrm{diag}(a,1)\,k\,\mathrm{diag}(t_0,1)\bigr)}\,d\,\mathrm{sPartMeasure}\,K\,\emptyset(a)\Bigr)d\,\mathrm{maximalCompactAtHaar}\,K\,\emptyset(k).$$
--   Here the outer integral on the left is over ideles with respect to [`NumberField.Idele.sPartMeasure K S`](def/NumberField_IdeleProductMeasure.html#L458), the push-forward under `partAt K S` of idelic Haar measure restricted to the ideles that are units outside $S$, and the inner integral is over the adelic maximal compact subgroup `adelicMaximalCompact K` with its Haar measure `maximalCompactHaar K`; on the right the outer integral is over `maximalCompactAt K ∅`, the adelic maximal compact subgroup all of whose finite components are trivial, with its Haar measure, and the inner integral is with respect to `sPartMeasure K ∅`. The powers $\|t_0\|^{s+1/2}$ and $\|a\|^{s+1/2}$ are complex powers of the real idele norms, while $\|t_0\|^{-w-1}$ and $\|a\|^{-w-1}$ are real powers, cast to $\mathbb{C}$.
--
--   This is the exact evaluation of the $S$-part (bad-place) Rankin–Selberg integral of a pair of $\mathrm{GL}_2$ vectors, the first obtained from $x_0$ by ball surgery at the places of $S$ with centre $t_0$ and depth $n_b$: the integral over the $S$-torus and the maximal compact subgroup collapses, up to a positive constant and the factor $\|t_0\|^{s+1/2}\|t_0\|^{-w-1}$, to an archimedean torus pairing against the datum $f_\infty$. It is used by [`AutomorphicForm.RankinSelberg.analyticOnNhd_sPartIntegral_pair_and_ne_zero_of_ball_surgery`](thm.html#AutomorphicForm.RankinSelberg.analyticOnNhd_sPartIntegral_pair_and_ne_zero_of_ball_surgery) to obtain analyticity of the $S$-part integral together with its non-vanishing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_RankinSelberg_exists_integral_torus_pair_eq_mul_integral_archTorus_of_ball_surgery.lean

import Definitions.Def_AutomorphicForm_RankinSelbergQuotientIntegral
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
open scoped ENNReal NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

theorem AutomorphicForm.RankinSelberg.exists_integral_torus_pair_eq_mul_integral_archTorus_of_ball_surgery
    (K : Type) [Field K] [NumberField K] :
    let α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (S : Finset (HeightOneSpectrum (𝓞 K)))
      (D₀ : Set (AdelicGL2 (𝓞 K) K))

      (ωx ωy : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : ℝ)
      (_hωx : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ωx z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w)
      (_hωy : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ωy z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w)
      (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hων : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((ωx z : ℂˣ) : ℂ) * (starRingEnd ℂ) ((ωy z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) =
          ((NumberField.TateGlobal.ideleNorm K z ^ (2 * w) : ℝ) : ℂ))

      (x₀ : AdelicGL2 (𝓞 K) K → ℂ) (_hx₀c : Continuous x₀)
      (nb : ℕ) (_hnb : 0 < nb)
      (_hx₀cong : ∀ (g k : AdelicGL2 (𝓞 K) K), k ∈ finiteAdelicGL2Subgroup K →
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → finComponent (𝓞 K) K v (glFin (𝓞 K) K k) = 1) →
        (∀ v ∈ S, ∀ i j : Fin 2,
          Valued.v ((((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j -
              (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
            ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        x₀ (g * k) = x₀ g)
      (_hxlarge : ∀ g : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K g = 1 → ∀ M : ℕ,
        ∃ Cg : ℝ, ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
          (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
          ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 → ∀ pl : InfinitePlace K,
            ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne a * k * g)‖ ≤
              Cg * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ (-(M : ℝ)))

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
      (_hxc : Continuous x)
      (_hxG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g)
      (_hxZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K), x (centralScalar (𝓞 K) K z * g) = ((ωx z : ℂˣ) : ℂ) * x g)
      (_hxKS : ∀ k ∈ maximalCompactAway K S, ∀ g : AdelicGL2 (𝓞 K) K, x (g * k) = x g)
      (n : ℕ) (_hn : 0 < n)
      (_hxlow : ∀ (γ : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K), γ.1 = 0 →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → γ.2 v = 0) →
        (∀ v ∈ S, Valued.v (γ.2 v) ≤
          ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        x (g * lowerUnipotentGL2 γ) = x g)

      (y : AdelicGL2 (𝓞 K) K → ℂ) (_hyc : Continuous y)
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
      (_hylarge : ∀ g : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K g = 1 → ∀ M : ℕ,
        ∃ Cg : ℝ, ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
          (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
          ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 → ∀ pl : InfinitePlace K,
            ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne a * k * g)‖ ≤
              Cg * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ (-(M : ℝ)))

      (finf : AdelicGL2 (𝓞 K) K → ℂ) (_hfc : Continuous finf)
      (φ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 K) K (etaFst 1 α hα s) (etaSnd ν α hα s) (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φ p.1 p.2))
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

      (δx Cx : ℝ) (_hδx : 0 < δx)
      (_hCx : ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
        ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
          ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne a * k * (diagOne t₀ * κ))‖ ≤
            Cx * ∏ pl : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) *
              (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δx))
      (δy Cy : ℝ) (_hδy : 0 < δy)
      (_hCy : ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
        ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
          ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne a * k * (diagOne t₀))‖ ≤
            Cy * ∏ pl : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) *
              (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δy)),
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ s : ℂ, 1 / 2 - (δx + δy) / 2 < s.re →
      (∫ t, ∫ k,
          whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
          (diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
              (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne t * (k : AdelicGL2 (𝓞 K) K))) *
              φ s (diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
            ((NumberField.TateGlobal.ideleNorm K t ^ (-w - 1) : ℝ) : ℂ)
          ∂(maximalCompactHaar K) ∂(NumberField.Idele.sPartMeasure K S)) =
        (κ₀ : ℂ) * (((NumberField.TateGlobal.ideleNorm K t₀ : ℝ) : ℂ) ^ (s + 1 / 2) *
            ((NumberField.TateGlobal.ideleNorm K t₀ ^ (-w - 1) : ℝ) : ℂ)) *
          ∫ k, finf (k : AdelicGL2 (𝓞 K) K) *
            (∫ a, ((NumberField.TateGlobal.ideleNorm K a : ℝ) : ℂ) ^ (s + 1 / 2) *
              ((NumberField.TateGlobal.ideleNorm K a ^ (-w - 1) : ℝ) : ℂ) *
              (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne a * (k : AdelicGL2 (𝓞 K) K) * (diagOne t₀ * κ)) *
                (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne a * (k : AdelicGL2 (𝓞 K) K) * diagOne t₀)))
            ∂(NumberField.Idele.sPartMeasure K ∅))
          ∂(maximalCompactAtHaar K ∅) := by sorry
