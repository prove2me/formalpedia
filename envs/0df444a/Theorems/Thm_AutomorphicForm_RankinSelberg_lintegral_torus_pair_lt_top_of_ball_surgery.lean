-- Prove2me | Theorems.Thm_AutomorphicForm_RankinSelberg_lintegral_torus_pair_lt_top_of_ball_surgery
-- name    : AutomorphicForm.RankinSelberg.lintegral_torus_pair_lt_top_of_ball_surgery
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/9c728ce2-57a9-5f6f-baed-28447a42dfa5
-- title:
--   Absolute convergence of the ball-surgered torus S-part integral
-- statement:
--   Let $K$ be a number field and let $\alpha : (\mathbf A_K)^\times \to \mathbb R^\times$ be the character of ideles obtained from the module `distribHaarChar (AdeleRing (𝓞 K) K)` by composing with $\mathbb R_{\ge 0} \to \mathbb R$ and passing to units; the hypothesis `hα` asserts $\alpha(t) > 0$ for every idele $t$. Fixed further are: a finite set $S$ of finite places of $K$ (height-one primes of $\mathcal O_K$), a subset $D_0$ of $\mathrm{GL}_2(\mathbf A_K)$, characters $\omega_x, \omega_y, \nu : (\mathbf A_K)^\times \to \mathbb C^\times$ and a real number $w$.
--
--   Throughout, `whittakerCoefficient` is taken with respect to the carrier data `productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`, whose adelic measure is the additive Haar measure of $\mathbf A_K$ conditioned on the box `adelicBox K` (archimedean part in the fundamental domain of the lattice, finite part integral), with the standard additive character $\psi =$ [`NumberField.StandardAddChar.stdAddChar K`](def/NumberField_AdelicTraceFin.html#L198) and at the field element $1$: thus for $f$ on $\mathrm{GL}_2(\mathbf A_K)$ its value at $g$ is the average of $f(u(\xi) g)\,\psi(-\xi)$ over $\xi$ in the box, $u(\xi)$ the upper unipotent matrix with entry $\xi$. Write $W f$ for this coefficient, $\mathrm{diag}(t,1)$ for `diagOne t`, $\|t\|$ for [`NumberField.TateGlobal.ideleNorm K t`](def/NumberField_TateGlobalZeta.html#L19) (the value of the module character), and $\mathbf K =$ `adelicMaximalCompact K` for the subgroup of $g$ with integral finite part and with row-isometric archimedean component at every infinite place.
--
--   The hypotheses are grouped as follows; each group is stated in full or, where said, summarised.
--
--   Central characters: `_hωx` and `_hωy` require $\|\omega_x(z)\| = \|\omega_y(z)\| = \|z\|^{w}$ for all ideles $z$, and `_hων` requires $\omega_x(z)\,\overline{\omega_y(z)}\,\nu(z) = \|z\|^{2w}$.
--
--   The source vector $x_0$: a function $x_0 : \mathrm{GL}_2(\mathbf A_K) \to \mathbb C$, a positive natural number $nb$, and two conditions. `_hx₀cong` states that $x_0(gk) = x_0(g)$ whenever $k$ has trivial archimedean part, integral finite part, trivial component at every $v \notin S$, and, at every $v \in S$, all entries of $k - 1$ of $v$-valuation at most $\mathrm{ofAdd}(-nb)$. `_hxlarge` is the large-end decay: for every $g$ with trivial archimedean part and every $M \in \mathbb N$ there is $C_g$ with $\|W x_0(\mathrm{diag}(a,1)\,k\,g)\| \le C_g\,\|a\|^{w/2}\,\|a_{\mathrm{pl}}\|^{-M}$ for all $k$ with trivial finite part and row-isometric archimedean components, all ideles $a$ with finite part $1$, and all infinite places $\mathrm{pl}$.
--
--   The bad-place translate: an idele $t_0$ with archimedean part $1$ (`_ht₀inf`) and component $1$ at every $v \notin S$ (`_ht₀`), a natural number $m$ with $v$-valuation of $t_0$ at most $\mathrm{ofAdd}(m)$ for $v \in S$ (`_ht₀box`); an element $k_0$ of `maximalCompactAt K S` (in $\mathbf K$ and with trivial component outside $S$), and $\kappa$ equal to the image of the finite part of $k_0$ under [`AdelicDock.finEmbed`](def/AdelicDock_LocalEmbedding.html#L145), i.e. the matrix with archimedean part $1$ and finite part that of $k_0$.
--
--   The exponential-sum (ball) data: $r \in \mathbb N$, adeles $u_0,\dots,u_{r-1}$ and complex numbers $c_0,\dots,c_{r-1}$ with `_husupp` requiring each $u_i$ to have zero archimedean part and zero component outside $S$. `_hWmult` states that for every idele $t$ and every $g'$ commuting with all $u(u_i)$, the Whittaker coefficient of $g \mapsto \sum_i c_i\,x_0(g\,u(u_i)\,\kappa)$ at $\mathrm{diag}(t,1)g'$ equals $\bigl(\sum_i c_i\,\psi(t\,u_i)\bigr)$ times the Whittaker coefficient of $g \mapsto x_0(g\kappa)$ at $\mathrm{diag}(t,1)g'$. `_hμball` states that for every idele $t$ whose $v$-valuation is at most $\mathrm{ofAdd}(m)$ for all $v \in S$, the sum $\sum_i c_i\,\psi(t\,u_i)$ equals $1$ if the $v$-valuation of $t_v - t_{0,v}$ is at most that of $t_{0,v}$ times $\mathrm{ofAdd}(-nb)$ for every $v \in S$, and $0$ otherwise. `_hboxvan` states that $W x_0(\mathrm{diag}(t,1)\,k\,\kappa) = 0$ whenever $k$ has trivial finite part and row-isometric archimedean components and $t$ has $v$-valuation strictly larger than $\mathrm{ofAdd}(m)$ at some $v \in S$.
--
--   The first vector $x$: a function $x$ with `_hxsum` $x(g) = \sum_i c_i\,x_0(g\,(u(u_i)\kappa))$; `_hxG` left invariance under $\mathrm{GL}_2(K)$ embedded in $\mathrm{GL}_2(\mathbf A_K)$; `_hxZ` the central character law $x(z\cdot g) = \omega_x(z)\,x(g)$ for central scalars $z$; `_hxKS` right invariance under `maximalCompactAway K S` (elements of $\mathbf K$ with trivial archimedean part and trivial component at each $v \in S$); a positive natural number $n$; and `_hxlow` right invariance under lower unipotent matrices $\mathrm{low}(\gamma)$ for adeles $\gamma$ with zero archimedean part, zero component outside $S$ and $v$-valuation at most $\mathrm{ofAdd}(-n)$ at each $v \in S$.
--
--   The second vector $y$: a function $y$ with `_hyG` (invariance under $\mathrm{GL}_2(K)$), `_hyZ` (central character $\omega_y$), `_hyKS` (right invariance under `maximalCompactAway K S`), `_hycong` (the same congruence invariance at depth $nb$ as `_hx₀cong`, for $y$), `_hylow` (the same lower-unipotent invariance at depth $n$ as `_hxlow`), and `_hylarge` (the same large-end decay as `_hxlarge`, for $W y$).
--
--   The section family: a function $f_\infty =$ `finf` on $\mathrm{GL}_2(\mathbf A_K)$ and a family $\varphi : \mathbb C \to (\mathrm{GL}_2(\mathbf A_K) \to \mathbb C)$ with five conditions. `_hφ`: for each $s$, $\varphi_s$ is an induced section for the pair of characters $\alpha^{\,s+1/2}$ and $\nu\,\alpha^{-(s+1/2)}$, that is $\varphi_s(bg) = \alpha(b_{00})^{s+1/2}\,\nu(b_{11})\,\alpha(b_{11})^{-(s+1/2)}\,\varphi_s(g)$ for every upper triangular $b$ and every $g$. `_hφjc`: $(s,g) \mapsto \varphi_s(g)$ is continuous. `_hφKS`: each $\varphi_s$ is right invariant under `maximalCompactAway K S`. `_hφsupp`: $\varphi_s(k) = 0$ for $k$ with integral finite part and row-isometric archimedean components as soon as, at some $v \in S$, the $v$-valuation of $k_{10}$ fails to be at most that of $k_{11}$ times $\mathrm{ofAdd}(-n)$. `_hφval`: if $k$ has integral finite part and row-isometric archimedean components, $k_\infty$ has trivial finite part and the same archimedean part as $k$, local units $d_v$ satisfy $k_{11,v} = d_v$ for $v \in S$, and the bottom-row condition of depth $n$ holds at every $v \in S$, then $\varphi_s(k) = \bigl(\prod_{v \in S} \nu_v(d_v)\bigr) f_\infty(k_\infty)$, where $\nu_v =$ `localChar ν v`.
--
--   The small-end bounds: reals $\delta_x, C_x$ with $\delta_x > 0$ and `_hCx` asserting, for all $k$ with trivial finite part and row-isometric archimedean components and all ideles $a$ with finite part $1$,
--   $$\|W x_0(\mathrm{diag}(a,1)\,k\,(\mathrm{diag}(t_0,1)\kappa))\| \le C_x \prod_{\mathrm{pl}\mid\infty} \|a_{\mathrm{pl}}\|^{\,m_{\mathrm{pl}}w/2}\,\bigl(\min(1,\|a_{\mathrm{pl}}\|)\bigr)^{\delta_x},$$
--   with $m_{\mathrm{pl}}$ the multiplicity of the place; and reals $\delta_y, C_y$ with $\delta_y > 0$ and `_hCy` the analogous bound for $\|W y(\mathrm{diag}(a,1)\,k\,\mathrm{diag}(t_0,1))\|$ with exponent $\delta_y$.
--
--   Conclusion: for every $s \in \mathbb C$ with $\tfrac12 - \tfrac{\delta_x + \delta_y}{2} < \operatorname{Re} s$,
--   $$\int^{-}_{t} \int^{-}_{k \in \mathbf K} \bigl\| W x(\mathrm{diag}(t,1)k)\cdot \overline{W y(\mathrm{diag}(t,1)k)} \cdot \varphi_s(\mathrm{diag}(t,1)k) \bigr\|_{\mathrm e}\; \mathrm{ofReal}\bigl(\|t\|^{-w-1}\bigr)\, d(\mathrm{maximalCompactHaar}\ K)\, d(\mathrm{sPartMeasure}\ K\ S) < \infty,$$
--   the integrals being lower Lebesgue integrals in $[0,\infty]$: the inner one over the compact group $\mathbf K$ with its Haar measure, the outer one over the ideles with the measure [`NumberField.Idele.sPartMeasure K S`](def/NumberField_IdeleProductMeasure.html#L458), the image under `partAt K S` of the idelic Haar measure restricted to the ideles that are units outside $S$.
--
--   This is the absolute-convergence statement for the bad-place ($S$-part) Rankin–Selberg integral in its torus form, for a pair consisting of a vector obtained from $x_0$ by ball surgery at the places of $S$ and a second vector $y$, against an induced section of depth $n$; the admissible range of $s$ extends past the centre by $(\delta_x+\delta_y)/2$. It is used by [`AutomorphicForm.RankinSelberg.analyticOnNhd_sPartIntegral_pair_and_ne_zero_of_ball_surgery`](thm.html#AutomorphicForm.RankinSelberg.analyticOnNhd_sPartIntegral_pair_and_ne_zero_of_ball_surgery) and by [`AutomorphicForm.RankinSelberg.exists_integral_torus_pair_eq_mul_integral_archTorus_of_ball_surgery`](thm.html#AutomorphicForm.RankinSelberg.exists_integral_torus_pair_eq_mul_integral_archTorus_of_ball_surgery), which need finiteness before manipulating the integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_RankinSelberg_lintegral_torus_pair_lt_top_of_ball_surgery.lean

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

theorem AutomorphicForm.RankinSelberg.lintegral_torus_pair_lt_top_of_ball_surgery
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
      (_hylarge : ∀ g : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K g = 1 → ∀ M : ℕ,
        ∃ Cg : ℝ, ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
          (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
          ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 → ∀ pl : InfinitePlace K,
            ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne a * k * g)‖ ≤
              Cg * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ (-(M : ℝ)))

      (finf : AdelicGL2 (𝓞 K) K → ℂ)
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
    ∀ s : ℂ, 1 / 2 - (δx + δy) / 2 < s.re →
      (∫⁻ t, ∫⁻ k,
        ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
          (diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
            (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne t * (k : AdelicGL2 (𝓞 K) K))) *
            φ s (diagOne t * (k : AdelicGL2 (𝓞 K) K))‖ₑ *
          ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K t ^ (-w - 1))
        ∂(maximalCompactHaar K) ∂(NumberField.Idele.sPartMeasure K S)) < ∞ := by sorry
